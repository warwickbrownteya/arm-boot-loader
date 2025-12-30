/*
 * net.h - Network Stack for ARM Bootloader
 *
 * Minimal network implementation for boot-time operations:
 * - Ethernet frame handling
 * - ARP (Address Resolution Protocol)
 * - IP (Internet Protocol v4)
 * - UDP (User Datagram Protocol)
 * - DHCP (Dynamic Host Configuration Protocol)
 * - TFTP (Trivial File Transfer Protocol)
 */

#ifndef NET_H
#define NET_H

#include <stdint.h>
#include <stddef.h>

/* Network configuration */
#define NET_MAX_PACKET_SIZE     1536
#define NET_ARP_TABLE_SIZE      8
#define NET_TFTP_BLOCK_SIZE     512
#define NET_TIMEOUT_MS          5000
#define NET_RETRY_COUNT         5

/* Ethernet types */
#define ETH_TYPE_IP             0x0800
#define ETH_TYPE_ARP            0x0806

/* IP protocols */
#define IP_PROTO_ICMP           1
#define IP_PROTO_UDP            17

/* ARP operations */
#define ARP_OP_REQUEST          1
#define ARP_OP_REPLY            2

/* DHCP ports */
#define DHCP_CLIENT_PORT        68
#define DHCP_SERVER_PORT        67

/* TFTP ports and opcodes */
#define TFTP_PORT               69
#define TFTP_OP_RRQ             1
#define TFTP_OP_WRQ             2
#define TFTP_OP_DATA            3
#define TFTP_OP_ACK             4
#define TFTP_OP_ERROR           5

/* DHCP message types */
#define DHCP_DISCOVER           1
#define DHCP_OFFER              2
#define DHCP_REQUEST            3
#define DHCP_DECLINE            4
#define DHCP_ACK                5
#define DHCP_NAK                6
#define DHCP_RELEASE            7
#define DHCP_INFORM             8

/* DHCP options */
#define DHCP_OPT_SUBNET         1
#define DHCP_OPT_ROUTER         3
#define DHCP_OPT_DNS            6
#define DHCP_OPT_HOSTNAME       12
#define DHCP_OPT_REQ_IP         50
#define DHCP_OPT_LEASE          51
#define DHCP_OPT_MSG_TYPE       53
#define DHCP_OPT_SERVER_ID      54
#define DHCP_OPT_PARAM_REQ      55
#define DHCP_OPT_END            255

/* MAC address */
typedef struct {
    uint8_t addr[6];
} __attribute__((packed)) mac_addr_t;

/* IPv4 address */
typedef struct {
    uint8_t addr[4];
} __attribute__((packed)) ip_addr_t;

/* Ethernet header */
typedef struct {
    mac_addr_t  dst;
    mac_addr_t  src;
    uint16_t    type;
} __attribute__((packed)) eth_header_t;

/* ARP packet */
typedef struct {
    uint16_t    hw_type;        /* Hardware type (Ethernet = 1) */
    uint16_t    proto_type;     /* Protocol type (IPv4 = 0x0800) */
    uint8_t     hw_len;         /* Hardware address length (6) */
    uint8_t     proto_len;      /* Protocol address length (4) */
    uint16_t    op;             /* Operation */
    mac_addr_t  sender_mac;
    ip_addr_t   sender_ip;
    mac_addr_t  target_mac;
    ip_addr_t   target_ip;
} __attribute__((packed)) arp_packet_t;

/* IPv4 header */
typedef struct {
    uint8_t     ver_ihl;        /* Version (4) + IHL (5) */
    uint8_t     tos;            /* Type of service */
    uint16_t    len;            /* Total length */
    uint16_t    id;             /* Identification */
    uint16_t    frag_off;       /* Fragment offset */
    uint8_t     ttl;            /* Time to live */
    uint8_t     proto;          /* Protocol */
    uint16_t    checksum;       /* Header checksum */
    ip_addr_t   src;            /* Source IP */
    ip_addr_t   dst;            /* Destination IP */
} __attribute__((packed)) ip_header_t;

/* UDP header */
typedef struct {
    uint16_t    src_port;
    uint16_t    dst_port;
    uint16_t    len;
    uint16_t    checksum;
} __attribute__((packed)) udp_header_t;

/* DHCP packet */
typedef struct {
    uint8_t     op;             /* Message type: 1=request, 2=reply */
    uint8_t     htype;          /* Hardware type: 1=Ethernet */
    uint8_t     hlen;           /* Hardware address length: 6 */
    uint8_t     hops;           /* Hop count */
    uint32_t    xid;            /* Transaction ID */
    uint16_t    secs;           /* Seconds elapsed */
    uint16_t    flags;          /* Flags */
    ip_addr_t   ciaddr;         /* Client IP (if known) */
    ip_addr_t   yiaddr;         /* Your (client) IP */
    ip_addr_t   siaddr;         /* Next server IP */
    ip_addr_t   giaddr;         /* Relay agent IP */
    uint8_t     chaddr[16];     /* Client hardware address */
    uint8_t     sname[64];      /* Server hostname */
    uint8_t     file[128];      /* Boot filename */
    uint8_t     options[312];   /* DHCP options */
} __attribute__((packed)) dhcp_packet_t;

/* TFTP packet */
typedef struct {
    uint16_t    opcode;
    union {
        struct {
            char filename[2];   /* Variable length, followed by mode */
        } rrq;
        struct {
            uint16_t block;
            uint8_t  data[512];
        } data;
        struct {
            uint16_t block;
        } ack;
        struct {
            uint16_t code;
            char     msg[1];    /* Variable length */
        } error;
    } u;
} __attribute__((packed)) tftp_packet_t;

/* ARP table entry */
typedef struct {
    ip_addr_t   ip;
    mac_addr_t  mac;
    uint32_t    timestamp;
    int         valid;
} arp_entry_t;

/* Network state */
typedef struct {
    /* Hardware */
    mac_addr_t  our_mac;
    int         link_up;

    /* IP configuration */
    ip_addr_t   our_ip;
    ip_addr_t   netmask;
    ip_addr_t   gateway;
    ip_addr_t   server_ip;
    ip_addr_t   dns_ip;

    /* DHCP state */
    int         dhcp_done;
    uint32_t    dhcp_xid;
    uint32_t    dhcp_lease;

    /* TFTP state */
    uint16_t    tftp_block;
    uint16_t    tftp_port;      /* Our source port */
    uint16_t    tftp_server_port;

    /* ARP table */
    arp_entry_t arp_table[NET_ARP_TABLE_SIZE];

    /* Statistics */
    uint32_t    rx_packets;
    uint32_t    tx_packets;
    uint32_t    rx_errors;
    uint32_t    tx_errors;
} net_state_t;

/* Callback for received data */
typedef void (*tftp_callback_t)(uint8_t *data, size_t len, int final);

/*
 * Network driver interface - BSP must implement these
 */

/* Initialize network hardware */
int bsp_net_init(void);

/* Check if link is up */
int bsp_net_link_up(void);

/* Get MAC address */
void bsp_net_get_mac(mac_addr_t *mac);

/* Send raw Ethernet frame */
int bsp_net_send(const uint8_t *data, size_t len);

/* Receive raw Ethernet frame (non-blocking, returns 0 if no packet) */
int bsp_net_recv(uint8_t *data, size_t maxlen);

/* Get current time in milliseconds (for timeouts) */
uint32_t bsp_net_get_time_ms(void);

/*
 * Network stack API
 */

/* Initialize network stack */
int net_init(void);

/* Get network state */
net_state_t *net_get_state(void);

/* Set static IP configuration */
void net_set_ip(const ip_addr_t *ip, const ip_addr_t *netmask, const ip_addr_t *gateway);

/* Run DHCP to get IP configuration */
int net_dhcp(void);

/* Ping a host */
int net_ping(const ip_addr_t *ip, int count);

/* Download file via TFTP */
int net_tftp_get(const ip_addr_t *server, const char *filename,
                 uint8_t *buffer, size_t maxlen, size_t *received);

/* Process incoming packets (call periodically) */
void net_poll(void);

/* Utility functions */
void net_print_mac(const mac_addr_t *mac);
void net_print_ip(const ip_addr_t *ip);
int net_parse_ip(const char *str, ip_addr_t *ip);
int net_ip_equal(const ip_addr_t *a, const ip_addr_t *b);
void net_ip_copy(ip_addr_t *dst, const ip_addr_t *src);
uint16_t net_htons(uint16_t val);
uint32_t net_htonl(uint32_t val);
uint16_t net_ntohs(uint16_t val);
uint32_t net_ntohl(uint32_t val);

/* Broadcast/zero addresses */
extern const mac_addr_t MAC_BROADCAST;
extern const mac_addr_t MAC_ZERO;
extern const ip_addr_t IP_BROADCAST;
extern const ip_addr_t IP_ZERO;

#endif /* NET_H */
