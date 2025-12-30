#!/bin/bash
sleep 2
echo "mmc init"
sleep 2
echo "mmcinfo"
sleep 2
echo "fatls"
sleep 2
echo "fatload 0 0x40200000 HELLO.TXT"
sleep 2
echo "md 0x40200000 0x8"
sleep 2
