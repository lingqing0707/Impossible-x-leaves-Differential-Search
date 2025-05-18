#!/bin/bash
a=Valid.
r=8
echo "================================="
for ((c=9;c<16;c++)) do
	for ((d=10;d<16;d++)) do
		echo "=====$r-round : in_diff = ($c, $d) ------> out_diff = ($c, $d)====="
		echo "=====================================" >> impossible_pairs_new.txt
		echo "=====================================" >> possible_pairs_new.txt
		echo "$r-round : in_diff = ($c, $d) ------> out_diff = ($c, $d)" >> impossible_pairs_new.txt
		echo "$r-round : in_diff = ($c, $d) ------> out_diff = ($c, $d)" >> possible_pairs_new.txt
		echo "-------------------------------------" >> impossible_pairs_new.txt
		echo "-------------------------------------" >> possible_pairs_new.txt
		possible_num=0
		impossible_num=0
		for ((t=0;t<16;t++)) do
			for ((p=0;p<16;p++)) do
				python3 GIFT_AND_key_x_leaves_DC_SET.py 1 8 $c $d $c $d $t $p
				result=`stp GIFT_AND_key_x_leaves_DC_SET.cvc`
				if [[ "$result" = "$a" ]]; then
					let impossible_num+=1
					echo "$r-round : ($t, $(($t^$c)), $(($t^$d))) ---/---> ($p, $(($p^$c)), $(($p^$d)))" >> impossible_pairs_new.txt
				else
					let possible_num+=1
					echo "$r-round : ($t, $(($t^$c)), $(($t^$d))) ------> ($p, $(($p^$c)), $(($p^$d)))" >> possible_pairs_new.txt
				fi
			done
		done
		echo "-------------------------------------"  >> possible_pairs_new.txt
		echo " possible number : $possible_num"  >> possible_pairs_new.txt
		echo "-------------------------------------"  >> impossible_pairs_new.txt
		echo " impossible number : $impossible_num"  >> impossible_pairs_new.txt
		echo "=====================================" >> impossible_pairs_new.txt
		echo "=====================================" >> possible_pairs_new.txt
		echo "                                     " >> impossible_pairs_new.txt
		echo "                                     " >> possible_pairs_new.txt
	done
done

echo "================================="
