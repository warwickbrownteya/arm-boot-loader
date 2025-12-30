/*
 * net.c - Network Stack Implementation for ARM Bootloader
 *
 * Implements minimal network protocols for boot-time operations.
 */

#include "net.h"
#include "boot_common.h"
#include "shell.h"
#include "env.h"

/* Broadcast/zero addresses */
const mac_addr_t MAC_BROADCAST = {{ 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF }};
const mac_addr_t MAC_ZERO = {{ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 }};
const ip_addr_t IP_BROADCAST = {{ 255, 255, 255, 255 }};
const ip_addr_t IP_ZERO = {{ 0, 0, 0, 0 }};

/* Global network state */
static net_state_t net_state;

/* Packet buffer */
static uint8_t tx_buffer[NET_MAX_PACKET_SIZE];
static uint8_t rx_buffer[NET_MAX_PACKET_SIZE];

/*
 * Byte order conversion (network is big-endian)
 */

uint16_t net_htons(uint16_t val) {
    return ((val & 0xFF) << 8) | ((val >> 8) & 0xFF);
}

uint32_t net_htonl(uint32_t val) {
    return ((val & 0xFF) << 24) |
           ((val & 0xFF00) << 8) |
           ((val >> 8) & 0xFF00) |
           ((val >> 24) & 0xFF);
}

uint16_t net_ntohs(uint16_t val) {
    return net_htons(val);  /* Same operation */
}

uint32_t net_ntohl(uint32_t val) {
    return net_htonl(val);  /* Same operation */
}

/*
 * Utility functions
 */

int net_ip_equal(const ip_addr_t *a, const ip_addr_t *b) {
    return a->addr[0] == b->addr[0] &&
           a->addr[1] == b->addr[1] &&
           a->addr[2] == b->addr[2] &&
           a->addr[3] == b->addr[3];
}

void net_ip_copy(ip_addr_t *dst, const ip_addr_t *src) {
    dst->addr[0] = src->addr[0];
    dst->addr[1] = src->addr[1];
    dst->addr[2] = src->addr[2];
    dst->addr[3] = src->addr[3];
}

static void mac_copy(mac_addr_t *dst, const mac_addr_t *src) {
    for (int i = 0; i < 6; i++) {
        dst->addr[i] = src->addr[i];
    }
}

static int mac_equal(const mac_addr_t *a, const mac_addr_t *b) {
    for (int i = 0; i < 6; i++) {
        if (a->addr[i] != b->addr[i]) return 0;
    }
    return 1;
}

void net_print_mac(const mac_addr_t *mac) {
    shell_printf("%02x:%02x:%02x:%02x:%02x:%02x",
                 mac->addr[0], mac->addr[1], mac->addr[2],
                 mac->addr[3], mac->addr[4], mac->addr[5]);
}

void net_print_ip(const ip_addr_t *ip) {
    shell_printf("%d.%d.%d.%d",
                 ip->addr[0], ip->addr[1], ip->addr[2], ip->addr[3]);
}

int net_parse_ip(const char *str, ip_addr_t *ip) {
    int octets[4];
    int n = 0;
    int val = 0;
    int digits = 0;

    while (*str && n < 4) {
        if (*str >= '0' && *str <= '9') {
            val = val * 10 + (*str - '0');
            digits++;
            if (val > 255) return -1;
        } else if (*str == '.') {
            if (digits == 0) return -1;
            octets[n++] = val;
            val = 0;
            digits = 0;
        } else {
            break;
        }
        str++;
    }

    if (digits > 0 && n < 4) {
        octets[n++] = val;
    }

    if (n != 4) return -1;

    ip->addr[0] = octets[0];
    ip->addr[1] = octets[1];
    ip->addr[2] = octets[2];
    ip->addr[3] = octets[3];

    return 0;
}

/*
 * Checksum calculation
 */

static uint16_t checksum(const void *data, size_t len) {
    const uint16_t *p = (const uint16_t *)data;
    uint32_t sum = 0;

    while (len > 1) {
        sum += *p++;
        len -= 2;
    }

    if (len == 1) {
        sum += *(const uint8_t *)p;
    }

    while (sum >> 16) {
        sum = (sum & 0xFFFF) + (sum >> 16);
    }

    return ~sum;
}

static uint16_t udp_checksum(const ip_header_t *ip, const udp_header_t *udp,
                              const void *data, size_t datalen) {
    uint32_t sum = 0;

    /* Pseudo header */
    sum += (ip->src.addr[0] << 8) | ip->src.addr[1];
    sum += (ip->src.addr[2] << 8) | ip->src.addr[3];
    sum += (ip->dst.addr[0] << 8) | ip->dst.addr[1];
    sum += (ip->dst.addr[2] << 8) | ip->dst.addr[3];
    sum += IP_PROTO_UDP;
    sum += net_ntohs(udp->len);

    /* UDP header */
    sum += net_ntohs(udp->src_port);
    sum += net_ntohs(udp->dst_port);
    sum += net_ntohs(udp->len);

    /* Data */
    const uint16_t *p = (const uint16_t *)data;
    while (datalen > 1) {
        sum += *p++;
        datalen -= 2;
    }
    if (datalen == 1) {
        sum += *(const uint8_t *)p;
    }

    while (sum >> 16) {
        sum = (sum & 0xFFFF) + (sum >> 16);
    }

    return ~sum ? ~sum : 0xFFFF;
}

/*
 * ARP handling
 */

static arp_entry_t *arp_lookup(const ip_addr_t *ip) {
    for (int i = 0; i < NET_ARP_TABLE_SIZE; i++) {
        if (net_state.arp_table[i].valid &&
            net_ip_equal(&net_state.arp_table[i].ip, ip)) {
            return &net_state.arp_table[i];
        }
    }
    return NULL;
}

static void arp_add(const ip_addr_t *ip, const mac_addr_t *mac) {
    /* Look for existing entry */
    arp_entry_t *entry = arp_lookup(ip);
    if (entry) {
        mac_copy(&entry->mac, mac);
        entry->timestamp = bsp_net_get_time_ms();
        return;
    }

    /* Find free or oldest entry */
    int oldest = 0;
    uint32_t oldest_time = 0xFFFFFFFF;

    for (int i = 0; i < NET_ARP_TABLE_SIZE; i++) {
        if (!net_state.arp_table[i].valid) {
            oldest = i;
            break;
        }
        if (net_state.arp_table[i].timestamp < oldest_time) {
            oldest_time = net_state.arp_table[i].timestamp;
            oldest = i;
        }
    }

    entry = &net_state.arp_table[oldest];
    net_ip_copy(&entry->ip, ip);
    mac_copy(&entry->mac, mac);
    entry->timestamp = bsp_net_get_time_ms();
    entry->valid = 1;
}

static int arp_send_request(const ip_addr_t *target_ip) {
    uint8_t *pkt = tx_buffer;
    eth_header_t *eth = (eth_header_t *)pkt;
    arp_packet_t *arp = (arp_packet_t *)(pkt + sizeof(eth_header_t));

    /* Ethernet header */
    mac_copy(&eth->dst, &MAC_BROADCAST);
    mac_copy(&eth->src, &net_state.our_mac);
    eth->type = net_htons(ETH_TYPE_ARP);

    /* ARP request */
    arp->hw_type = net_htons(1);        /* Ethernet */
    arp->proto_type = net_htons(ETH_TYPE_IP);
    arp->hw_len = 6;
    arp->proto_len = 4;
    arp->op = net_htons(ARP_OP_REQUEST);
    mac_copy(&arp->sender_mac, &net_state.our_mac);
    net_ip_copy(&arp->sender_ip, &net_state.our_ip);
    mac_copy(&arp->target_mac, &MAC_ZERO);
    net_ip_copy(&arp->target_ip, target_ip);

    return bsp_net_send(pkt, sizeof(eth_header_t) + sizeof(arp_packet_t));
}

static void arp_handle(const arp_packet_t *arp) {
    uint16_t op = net_ntohs(arp->op);

    if (op == ARP_OP_REQUEST) {
        /* Is it for our IP? */
        if (net_ip_equal(&arp->target_ip, &net_state.our_ip)) {
            /* Send reply */
            uint8_t *pkt = tx_buffer;
            eth_header_t *eth = (eth_header_t *)pkt;
            arp_packet_t *reply = (arp_packet_t *)(pkt + sizeof(eth_header_t));

            mac_copy(&eth->dst, &arp->sender_mac);
            mac_copy(&eth->src, &net_state.our_mac);
            eth->type = net_htons(ETH_TYPE_ARP);

            reply->hw_type = net_htons(1);
            reply->proto_type = net_htons(ETH_TYPE_IP);
            reply->hw_len = 6;
            reply->proto_len = 4;
            reply->op = net_htons(ARP_OP_REPLY);
            mac_copy(&reply->sender_mac, &net_state.our_mac);
            net_ip_copy(&reply->sender_ip, &net_state.our_ip);
            mac_copy(&reply->target_mac, &arp->sender_mac);
            net_ip_copy(&reply->target_ip, &arp->sender_ip);

            bsp_net_send(pkt, sizeof(eth_header_t) + sizeof(arp_packet_t));
        }

        /* Learn sender's MAC */
        arp_add(&arp->sender_ip, &arp->sender_mac);

    } else if (op == ARP_OP_REPLY) {
        /* Learn sender's MAC */
        arp_add(&arp->sender_ip, &arp->sender_mac);
    }
}

static int arp_resolve(const ip_addr_t *ip, mac_addr_t *mac) {
    /* Check if on same subnet */
    int same_subnet = 1;
    for (int i = 0; i < 4; i++) {
        if ((net_state.our_ip.addr[i] & net_state.netmask.addr[i]) !=
            (ip->addr[i] & net_state.netmask.addr[i])) {
            same_subnet = 0;
            break;
        }
    }

    /* Use gateway for different subnet */
    const ip_addr_t *target = same_subnet ? ip : &net_state.gateway;

    /* Check ARP cache */
    arp_entry_t *entry = arp_lookup(target);
    if (entry) {
        mac_copy(mac, &entry->mac);
        return 0;
    }

    /* Send ARP request and wait for reply */
    for (int retry = 0; retry < NET_RETRY_COUNT; retry++) {
        arp_send_request(target);

        uint32_t start = bsp_net_get_time_ms();
        while ((bsp_net_get_time_ms() - start) < 1000) {
            net_poll();
            entry = arp_lookup(target);
            if (entry) {
                mac_copy(mac, &entry->mac);
                return 0;
            }
        }
    }

    return -1;  /* Resolution failed */
}

/*
 * IP/UDP sending
 */

static uint16_t ip_id = 0;

static int send_udp(const ip_addr_t *dst_ip, uint16_t src_port, uint16_t dst_port,
                    const void *data, size_t datalen) {
    mac_addr_t dst_mac;

    /* Resolve destination MAC */
    if (net_ip_equal(dst_ip, &IP_BROADCAST)) {
        mac_copy(&dst_mac, &MAC_BROADCAST);
    } else if (arp_resolve(dst_ip, &dst_mac) < 0) {
        return -1;
    }

    /* Build packet */
    uint8_t *pkt = tx_buffer;
    eth_header_t *eth = (eth_header_t *)pkt;
    ip_header_t *ip = (ip_header_t *)(pkt + sizeof(eth_header_t));
    udp_header_t *udp = (udp_header_t *)((uint8_t *)ip + sizeof(ip_header_t));
    uint8_t *payload = (uint8_t *)udp + sizeof(udp_header_t);

    /* Ethernet header */
    mac_copy(&eth->dst, &dst_mac);
    mac_copy(&eth->src, &net_state.our_mac);
    eth->type = net_htons(ETH_TYPE_IP);

    /* IP header */
    ip->ver_ihl = 0x45;     /* IPv4, 5 32-bit words */
    ip->tos = 0;
    ip->len = net_htons(sizeof(ip_header_t) + sizeof(udp_header_t) + datalen);
    ip->id = net_htons(ip_id++);
    ip->frag_off = 0;
    ip->ttl = 64;
    ip->proto = IP_PROTO_UDP;
    ip->checksum = 0;
    net_ip_copy(&ip->src, &net_state.our_ip);
    net_ip_copy(&ip->dst, dst_ip);
    ip->checksum = checksum(ip, sizeof(ip_header_t));

    /* UDP header */
    udp->src_port = net_htons(src_port);
    udp->dst_port = net_htons(dst_port);
    udp->len = net_htons(sizeof(udp_header_t) + datalen);
    udp->checksum = 0;

    /* Copy payload */
    const uint8_t *src = (const uint8_t *)data;
    for (size_t i = 0; i < datalen; i++) {
        payload[i] = src[i];
    }

    /* UDP checksum (optional but recommended) */
    udp->checksum = udp_checksum(ip, udp, payload, datalen);

    size_t total = sizeof(eth_header_t) + sizeof(ip_header_t) +
                   sizeof(udp_header_t) + datalen;

    return bsp_net_send(pkt, total);
}

/*
 * DHCP implementation
 */

static uint8_t dhcp_buffer[sizeof(dhcp_packet_t)];

static void dhcp_add_option(uint8_t **opt, uint8_t code, uint8_t len, const void *data) {
    *(*opt)++ = code;
    if (len > 0) {
        *(*opt)++ = len;
        const uint8_t *p = (const uint8_t *)data;
        for (int i = 0; i < len; i++) {
            *(*opt)++ = p[i];
        }
    }
}

static int dhcp_send_discover(void) {
    dhcp_packet_t *dhcp = (dhcp_packet_t *)dhcp_buffer;
    uint8_t *opt;

    /* Clear buffer */
    for (size_t i = 0; i < sizeof(dhcp_buffer); i++) {
        dhcp_buffer[i] = 0;
    }

    /* DHCP header */
    dhcp->op = 1;           /* BOOTREQUEST */
    dhcp->htype = 1;        /* Ethernet */
    dhcp->hlen = 6;
    dhcp->hops = 0;
    dhcp->xid = net_htonl(net_state.dhcp_xid);
    dhcp->secs = 0;
    dhcp->flags = net_htons(0x8000);  /* Broadcast */

    /* Copy MAC */
    for (int i = 0; i < 6; i++) {
        dhcp->chaddr[i] = net_state.our_mac.addr[i];
    }

    /* DHCP magic cookie */
    opt = dhcp->options;
    *opt++ = 99; *opt++ = 130; *opt++ = 83; *opt++ = 99;

    /* Options */
    uint8_t msg_type = DHCP_DISCOVER;
    dhcp_add_option(&opt, DHCP_OPT_MSG_TYPE, 1, &msg_type);

    /* Parameter request list */
    uint8_t param_req[] = { DHCP_OPT_SUBNET, DHCP_OPT_ROUTER, DHCP_OPT_DNS };
    dhcp_add_option(&opt, DHCP_OPT_PARAM_REQ, sizeof(param_req), param_req);

    *opt++ = DHCP_OPT_END;

    return send_udp(&IP_BROADCAST, DHCP_CLIENT_PORT, DHCP_SERVER_PORT,
                    dhcp, sizeof(dhcp_packet_t));
}

static int dhcp_send_request(const ip_addr_t *server, const ip_addr_t *requested) {
    dhcp_packet_t *dhcp = (dhcp_packet_t *)dhcp_buffer;
    uint8_t *opt;

    /* Clear buffer */
    for (size_t i = 0; i < sizeof(dhcp_buffer); i++) {
        dhcp_buffer[i] = 0;
    }

    /* DHCP header */
    dhcp->op = 1;
    dhcp->htype = 1;
    dhcp->hlen = 6;
    dhcp->xid = net_htonl(net_state.dhcp_xid);
    dhcp->flags = net_htons(0x8000);

    for (int i = 0; i < 6; i++) {
        dhcp->chaddr[i] = net_state.our_mac.addr[i];
    }

    /* Options */
    opt = dhcp->options;
    *opt++ = 99; *opt++ = 130; *opt++ = 83; *opt++ = 99;

    uint8_t msg_type = DHCP_REQUEST;
    dhcp_add_option(&opt, DHCP_OPT_MSG_TYPE, 1, &msg_type);
    dhcp_add_option(&opt, DHCP_OPT_REQ_IP, 4, requested);
    dhcp_add_option(&opt, DHCP_OPT_SERVER_ID, 4, server);

    *opt++ = DHCP_OPT_END;

    return send_udp(&IP_BROADCAST, DHCP_CLIENT_PORT, DHCP_SERVER_PORT,
                    dhcp, sizeof(dhcp_packet_t));
}

static int dhcp_state = 0;
static ip_addr_t dhcp_offered_ip;
static ip_addr_t dhcp_server_ip;

static void dhcp_handle(const dhcp_packet_t *dhcp, size_t len) {
    (void)len;

    /* Check transaction ID */
    if (net_ntohl(dhcp->xid) != net_state.dhcp_xid) {
        return;
    }

    /* Check it's for us */
    int match = 1;
    for (int i = 0; i < 6; i++) {
        if (dhcp->chaddr[i] != net_state.our_mac.addr[i]) {
            match = 0;
            break;
        }
    }
    if (!match) return;

    /* Parse options */
    const uint8_t *opt = dhcp->options;

    /* Check magic cookie */
    if (opt[0] != 99 || opt[1] != 130 || opt[2] != 83 || opt[3] != 99) {
        return;
    }
    opt += 4;

    uint8_t msg_type = 0;
    ip_addr_t subnet = IP_ZERO;
    ip_addr_t router = IP_ZERO;
    ip_addr_t server_id = IP_ZERO;
    uint32_t lease = 0;

    while (*opt != DHCP_OPT_END && opt < dhcp->options + sizeof(dhcp->options)) {
        uint8_t code = *opt++;
        uint8_t olen = *opt++;

        switch (code) {
            case DHCP_OPT_MSG_TYPE:
                msg_type = *opt;
                break;
            case DHCP_OPT_SUBNET:
                for (int i = 0; i < 4; i++) subnet.addr[i] = opt[i];
                break;
            case DHCP_OPT_ROUTER:
                for (int i = 0; i < 4; i++) router.addr[i] = opt[i];
                break;
            case DHCP_OPT_SERVER_ID:
                for (int i = 0; i < 4; i++) server_id.addr[i] = opt[i];
                break;
            case DHCP_OPT_LEASE:
                lease = (opt[0] << 24) | (opt[1] << 16) | (opt[2] << 8) | opt[3];
                break;
        }

        opt += olen;
    }

    if (msg_type == DHCP_OFFER && dhcp_state == 0) {
        /* Got offer */
        shell_printf("DHCP: Offered ");
        net_print_ip(&dhcp->yiaddr);
        shell_printf(" from ");
        net_print_ip(&server_id);
        shell_printf("\n");

        net_ip_copy(&dhcp_offered_ip, &dhcp->yiaddr);
        net_ip_copy(&dhcp_server_ip, &server_id);
        dhcp_state = 1;

        /* Send request */
        dhcp_send_request(&server_id, &dhcp->yiaddr);

    } else if (msg_type == DHCP_ACK && dhcp_state == 1) {
        /* Got ACK */
        shell_printf("DHCP: Configured ");
        net_print_ip(&dhcp->yiaddr);
        shell_printf("\n");

        net_ip_copy(&net_state.our_ip, &dhcp->yiaddr);
        net_ip_copy(&net_state.netmask, &subnet);
        net_ip_copy(&net_state.gateway, &router);
        net_ip_copy(&net_state.server_ip, &server_id);
        net_state.dhcp_lease = lease;
        net_state.dhcp_done = 1;
        dhcp_state = 2;

        /* Update environment */
        char ip_str[16];
        shell_snprintf(ip_str, sizeof(ip_str), "%d.%d.%d.%d",
                      dhcp->yiaddr.addr[0], dhcp->yiaddr.addr[1],
                      dhcp->yiaddr.addr[2], dhcp->yiaddr.addr[3]);
        env_set("ipaddr", ip_str);

        shell_snprintf(ip_str, sizeof(ip_str), "%d.%d.%d.%d",
                      router.addr[0], router.addr[1],
                      router.addr[2], router.addr[3]);
        env_set("gatewayip", ip_str);

        shell_snprintf(ip_str, sizeof(ip_str), "%d.%d.%d.%d",
                      server_id.addr[0], server_id.addr[1],
                      server_id.addr[2], server_id.addr[3]);
        env_set("serverip", ip_str);

    } else if (msg_type == DHCP_NAK) {
        shell_printf("DHCP: Request denied\n");
        dhcp_state = 0;
    }
}

int net_dhcp(void) {
    if (!net_state.link_up) {
        shell_printf("Error: No network link\n");
        return -1;
    }

    /* Generate transaction ID */
    net_state.dhcp_xid = bsp_net_get_time_ms() ^ 0xDEADBEEF;

    /* Clear IP while doing DHCP */
    net_state.our_ip = IP_ZERO;
    dhcp_state = 0;

    shell_printf("DHCP: Discovering...\n");

    for (int retry = 0; retry < NET_RETRY_COUNT; retry++) {
        dhcp_send_discover();

        uint32_t start = bsp_net_get_time_ms();
        while ((bsp_net_get_time_ms() - start) < NET_TIMEOUT_MS) {
            net_poll();
            if (net_state.dhcp_done) {
                return 0;
            }
        }

        shell_printf("DHCP: Timeout, retrying...\n");
    }

    shell_printf("DHCP: Failed\n");
    return -1;
}

/*
 * TFTP implementation
 */

static uint8_t *tftp_buffer;
static size_t tftp_maxlen;
static size_t tftp_received;
static int tftp_done;
static int tftp_error;

static int tftp_send_rrq(const ip_addr_t *server, const char *filename) {
    uint8_t pkt[128];
    size_t len = 0;

    /* Opcode */
    pkt[len++] = 0;
    pkt[len++] = TFTP_OP_RRQ;

    /* Filename */
    while (*filename && len < sizeof(pkt) - 10) {
        pkt[len++] = *filename++;
    }
    pkt[len++] = 0;

    /* Mode */
    const char *mode = "octet";
    while (*mode) {
        pkt[len++] = *mode++;
    }
    pkt[len++] = 0;

    return send_udp(server, net_state.tftp_port, TFTP_PORT, pkt, len);
}

static int tftp_send_ack(const ip_addr_t *server, uint16_t block) {
    uint8_t pkt[4];
    pkt[0] = 0;
    pkt[1] = TFTP_OP_ACK;
    pkt[2] = (block >> 8) & 0xFF;
    pkt[3] = block & 0xFF;

    return send_udp(server, net_state.tftp_port, net_state.tftp_server_port, pkt, 4);
}

static void tftp_handle(const ip_addr_t *src_ip, uint16_t src_port,
                        const uint8_t *data, size_t len) {
    if (len < 4) return;

    uint16_t opcode = (data[0] << 8) | data[1];

    if (opcode == TFTP_OP_DATA) {
        uint16_t block = (data[2] << 8) | data[3];

        /* First data packet - remember server port */
        if (block == 1 && net_state.tftp_block == 0) {
            net_state.tftp_server_port = src_port;
        }

        /* Check it's the expected block */
        if (block == net_state.tftp_block + 1) {
            size_t datalen = len - 4;

            /* Copy data */
            if (tftp_received + datalen <= tftp_maxlen) {
                for (size_t i = 0; i < datalen; i++) {
                    tftp_buffer[tftp_received++] = data[4 + i];
                }
            } else {
                tftp_error = 1;
                tftp_done = 1;
                return;
            }

            net_state.tftp_block = block;

            /* Send ACK */
            tftp_send_ack(src_ip, block);

            /* Last block? */
            if (datalen < NET_TFTP_BLOCK_SIZE) {
                tftp_done = 1;
            }

            /* Progress indicator */
            if ((block & 0x1F) == 0) {
                shell_printf(".");
            }
        }

    } else if (opcode == TFTP_OP_ERROR) {
        uint16_t errcode = (data[2] << 8) | data[3];
        shell_printf("\nTFTP Error %d: ", errcode);
        if (len > 4) {
            shell_printf("%s", (const char *)&data[4]);
        }
        shell_printf("\n");
        tftp_error = 1;
        tftp_done = 1;
    }
}

int net_tftp_get(const ip_addr_t *server, const char *filename,
                 uint8_t *buffer, size_t maxlen, size_t *received) {
    if (!net_state.link_up || net_ip_equal(&net_state.our_ip, &IP_ZERO)) {
        shell_printf("Error: No network configuration\n");
        return -1;
    }

    /* Initialize state */
    tftp_buffer = buffer;
    tftp_maxlen = maxlen;
    tftp_received = 0;
    tftp_done = 0;
    tftp_error = 0;
    net_state.tftp_block = 0;
    net_state.tftp_port = 49152 + (bsp_net_get_time_ms() & 0x3FFF);  /* Ephemeral port */

    shell_printf("TFTP: Downloading %s from ", filename);
    net_print_ip(server);
    shell_printf("\n");

    for (int retry = 0; retry < NET_RETRY_COUNT; retry++) {
        tftp_send_rrq(server, filename);

        uint32_t start = bsp_net_get_time_ms();
        uint32_t last_progress = net_state.tftp_block;

        while ((bsp_net_get_time_ms() - start) < NET_TIMEOUT_MS) {
            net_poll();

            if (tftp_done) {
                if (tftp_error) {
                    return -1;
                }
                shell_printf("\nTFTP: Received %u bytes\n", (unsigned)tftp_received);
                if (received) *received = tftp_received;
                return 0;
            }

            /* Reset timeout on progress */
            if (net_state.tftp_block != last_progress) {
                start = bsp_net_get_time_ms();
                last_progress = net_state.tftp_block;
            }
        }

        shell_printf("\nTFTP: Timeout, retrying...\n");
    }

    shell_printf("TFTP: Failed\n");
    return -1;
}

/*
 * Packet reception and dispatch
 */

void net_poll(void) {
    int len = bsp_net_recv(rx_buffer, sizeof(rx_buffer));
    if (len <= 0) return;

    net_state.rx_packets++;

    eth_header_t *eth = (eth_header_t *)rx_buffer;

    /* Check destination MAC */
    if (!mac_equal(&eth->dst, &net_state.our_mac) &&
        !mac_equal(&eth->dst, &MAC_BROADCAST)) {
        return;
    }

    uint16_t type = net_ntohs(eth->type);

    if (type == ETH_TYPE_ARP) {
        arp_packet_t *arp = (arp_packet_t *)(rx_buffer + sizeof(eth_header_t));
        arp_handle(arp);

    } else if (type == ETH_TYPE_IP) {
        ip_header_t *ip = (ip_header_t *)(rx_buffer + sizeof(eth_header_t));

        /* Verify IP header */
        if ((ip->ver_ihl >> 4) != 4) return;  /* Must be IPv4 */

        /* Check destination IP */
        if (!net_ip_equal(&ip->dst, &net_state.our_ip) &&
            !net_ip_equal(&ip->dst, &IP_BROADCAST)) {
            return;
        }

        if (ip->proto == IP_PROTO_UDP) {
            size_t ip_hlen = (ip->ver_ihl & 0x0F) * 4;
            udp_header_t *udp = (udp_header_t *)((uint8_t *)ip + ip_hlen);
            uint8_t *data = (uint8_t *)udp + sizeof(udp_header_t);
            size_t udp_len = net_ntohs(udp->len) - sizeof(udp_header_t);

            uint16_t dst_port = net_ntohs(udp->dst_port);
            uint16_t src_port = net_ntohs(udp->src_port);

            if (dst_port == DHCP_CLIENT_PORT) {
                dhcp_handle((dhcp_packet_t *)data, udp_len);
            } else if (dst_port == net_state.tftp_port) {
                tftp_handle(&ip->src, src_port, data, udp_len);
            }
        }
    }
}

/*
 * Initialization
 */

int net_init(void) {
    /* Clear state */
    for (size_t i = 0; i < sizeof(net_state); i++) {
        ((uint8_t *)&net_state)[i] = 0;
    }

    /* Initialize hardware */
    if (bsp_net_init() < 0) {
        shell_printf("Network: Init failed\n");
        return -1;
    }

    /* Get MAC address */
    bsp_net_get_mac(&net_state.our_mac);

    /* Check link */
    net_state.link_up = bsp_net_link_up();

    shell_printf("Network: MAC ");
    net_print_mac(&net_state.our_mac);
    shell_printf(", Link %s\n", net_state.link_up ? "UP" : "DOWN");

    return 0;
}

net_state_t *net_get_state(void) {
    return &net_state;
}

void net_set_ip(const ip_addr_t *ip, const ip_addr_t *netmask, const ip_addr_t *gateway) {
    net_ip_copy(&net_state.our_ip, ip);
    net_ip_copy(&net_state.netmask, netmask);
    net_ip_copy(&net_state.gateway, gateway);
}

/*
 * Ping implementation
 */

int net_ping(const ip_addr_t *ip, int count) {
    (void)ip;
    (void)count;
    /* TODO: Implement ICMP echo */
    shell_printf("Ping not implemented yet\n");
    return -1;
}
