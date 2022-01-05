#!/bin/sh

echo "End-Easy"
target/release/victor_rs conspiracy-bench Test\ Sets/Test_L3_R1

echo "Middle-Easy"
target/release/victor_rs conspiracy-bench Test\ Sets/Test_L2_R1

#echo "Middle-Medium"
#target/release/victor_rs knowledge-bench Test\ Sets/Test_L2_R2
#echo "Begin-Easy"
#target/release/victor_rs knowledge-bench Test\ Sets/Test_L1_R1
#echo "Begin-Medium"
#target/release/victor_rs knowledge-bench Test\ Sets/Test_L1_R2
#echo "Begin-Hard"
#target/release/victor_rs knowledge-bench Test\ Sets/Test_L1_R3
