#!/bin/bash
sleep 4
echo "mmc init"
sleep 1
echo "mmcinfo"
sleep 1
echo "fatls"
sleep 3
echo "fatload 0 0x40200000 HELLO.TXT"
sleep 3
echo "md 0x40200000 0x8"
sleep 1
