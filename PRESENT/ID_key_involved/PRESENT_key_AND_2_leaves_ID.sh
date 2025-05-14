#!/bin/bash
a=Valid.
b=0
echo "-------------------------------"
for ((t=0;t<64;t++)) do
	for ((p=$(($t+1));p<64;p++)) do
		# for ((s=$(($p+1));s<64;s++)) do
		# echo "-----------------($t,$p,$s)-------------" >> PRESENT_key_AND_2_leaves_ID.txt
		# echo "-----------------($t,$p,$s)-------------" >> PRESENT_key_AND_2_leaves_DC.txt
		echo "-----------------($t,$p)-------------" >> PRESENT_key_AND_2_leaves_ID.txt
		echo "-----------------($t,$p)-------------" >> PRESENT_key_AND_2_leaves_DC.txt
		for ((u=0;u<4;u++)) do
			for ((times=0;times<20;times++)) do
				key=`python3 get_random_key.py`
				echo "------------key=$key--------------"
				echo "------------key=$key--------------" >> PRESENT_key_AND_2_leaves_ID.txt
				echo "------------key=$key--------------" >> PRESENT_key_AND_2_leaves_DC.txt
				for ((v=0;v<4;v++)) do
					if [[ "$u" != "$v" ]]; then
						python3 PRESENT_key_AND_2_leaves_ID.py $((2**$t)) $((2**$p)) $((2**$u)) $((2**$v)) 1 8 $key
						# python3 PRESENT_key_AND_2_leaves_ID.py $((2**$t)) $((2**$p)) $((2**$s)) $((2**$u)) $((2**$v)) 1 8
						result=`stp PRESENT_key_AND_2_leaves_ID.cvc`
						if [[ "$result" = "$a" ]]; then
							let b+=1
							# echo "8-r_ID: ($t,$p,$s) --\--> ($u,$v)" >> PRESENT_key_AND_2_leaves_ID.txt
							echo "8-r_ID: ($t,$p) --\--> ($u,$v)" >> PRESENT_key_AND_2_leaves_ID.txt
							k=`echo "obase=2;$key" | bc`
							kt=`echo $k | awk '{printf("%064d\n",$0)}'`
						else
							# echo "8-r_DC: ($t,$p,$s) -----> ($u,$v)" >> PRESENT_key_AND_2_leaves_DC.txt
							echo "8-r_ID: ($t,$p) -----> ($u,$v)" >> PRESENT_key_AND_2_leaves_DC.txt
						fi
					fi
				done
			done
		done
	done
done

echo "-------------------------------"
echo "ID number: $b"






