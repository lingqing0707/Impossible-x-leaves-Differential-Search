#!/bin/bash
a=Valid.
b=0
echo "-------------------------------"
for ((t=0;t<64;t++)) do
	for ((p=$(($t+1));p<64;p++)) do
		echo "-----------------($t,$p)-------------" >> PRESENT_normal_AND_2_leaves_ID.txt
		echo "-----------------($t,$p)-------------" >> PRESENT_normal_AND_2_leaves_DC.txt
		for ((u=0;u<64;u++)) do
			for ((v=0;v<64;v++)) do
				if [[ "$u" != "$v" ]]; then
					python3 PRESENT_normal_AND_2_leaves_ID.py $((2**$t)) $((2**$p)) $((2**$u)) $((2**$v)) 1 6
					result=`stp PRESENT_normal_AND_2_leaves_ID.cvc`
					if [[ "$result" = "$a" ]]; then
						let b+=1
						echo "6-r_ID: ($t,$p) --\--> ($u,$v)" >> PRESENT_normal_AND_2_leaves_ID.txt
					else
						echo "6-r_DC: ($t,$p) -----> ($u,$v)" >> PRESENT_normal_AND_2_leaves_DC.txt
					fi
				fi
			done
		done
	done
done

echo "-------------------------------"
echo "ID number: $b"




