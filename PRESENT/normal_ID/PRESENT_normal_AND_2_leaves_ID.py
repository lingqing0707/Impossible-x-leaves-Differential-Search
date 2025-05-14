# import numpy as np
import sys

Sbox = [0xc, 0x5, 0x6, 0xb, 0x9, 0x0, 0xa, 0xd, 0x3, 0xe, 0xf, 0x8, 0x4, 0x7, 0x1, 0x2]

def get_constraints_for_normal_SDDT(S):
	hex_string = '0x{:0%dx}' % 2
	constraints = list([])
	#constraints = constraints + ['input_diff, output_diff: BITVECTOR(4);']
	a = 'ASSERT( ( (input_diff=0x00) <=> (output_diff=0x00) )'
	for alpha in range(1,len(S)*len(S)):
		beta_list = list([])
		for x in range(len(S)):
			beta = (S[x] ^ S[x ^ int(alpha/len(S))]) * len(S) + (S[x] ^ S[x ^ int(alpha%len(S))])
			if beta not in beta_list:
				beta_list.append(beta)
		if len(beta_list)==1:
			a = a + 'AND ((input_diff='+hex_string.format(alpha)+') => (output_diff='+hex_string.format(beta_list[0])+')) '
		else:
			b = '(output_diff='+hex_string.format(beta_list[0])+')'
			for i in range(1,len(beta_list)):
				b = b + ' OR (output_diff=' + hex_string.format(beta_list[i])+')'
			a = a + 'AND ((input_diff='+hex_string.format(alpha)+') => (' + b + ')) '
	a = a + ');'
	return a
	
def get_constraints_for_key_SDDT(S):
	hex_string = '0x{:0%dx}' % 2
	hex_string_x = '0x{:0%dx}' % 1
	constraints = list([])
	#constraints = constraints + ['input_diff, output_diff: BITVECTOR(4);']
	a = 'ASSERT( ( (input_value_diff[7:0]=0x00) <=> (output_diff=0x00) )'
	for x in range(len(S)):
		for alpha in range(1,len(S)*len(S)):
			beta = (S[x] ^ S[x ^ int(alpha/len(S))]) * len(S) + (S[x] ^ S[x ^ int(alpha%len(S))])
			a = a + 'AND ((input_value_diff='+hex_string_x.format(x)+'@'+hex_string.format(alpha)+') => (output_diff='+hex_string.format(beta)+')) '
	a = a + ');'
	return a
		
#key_SDDT = get_constraints_for_key_SDDT(Sbox)
normal_SDDT = get_constraints_for_normal_SDDT(Sbox)
#print(SDDT)

class get_PRESENT():
	def __init__(self,blocksize,keysize,SDDT,Sbox):
		self.blocksize = blocksize
		self.cellsize = int(blocksize / 16)
		self.keysize = keysize
		self.Rounds = 31
		self.SDDT = SDDT
		self.Sbox = Sbox
		
	def collectvariables(self,r):
		constraints = list([])
		constraints = constraints + ['%declare r-th varibales']
		constraints = constraints + ['Is_'+str(r)+':BITVECTOR('+str(self.blocksize)+');']
		constraints = constraints + ['AIs_'+str(r)+':BITVECTOR('+str(self.blocksize)+');']
		return constraints
		
		
	def genDiff_Pass(self,r):
		assert r >=1
		constraints = list([])
		
		constraints = constraints + ['%r-th Diff_Passption']
		constraints = constraints + ['midSB_'+str(r)+':BITVECTOR('+str(self.blocksize)+');']
		constraints = constraints + ['AmidSB_'+str(r)+':BITVECTOR('+str(self.blocksize)+');']
		for i in range(16):
			constraints = constraints + [self.SDDT.replace('input_diff','Is_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+']@AIs_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+']').replace('output_diff', 'midSB_'+str(r)+'['+str(i*4+3)+':'+str(i*4)+']@AmidSB_'+str(r)+'['+str(i*4+3)+':'+str(i*4)+']')]
		constraints = constraints + ['ASSERT(Is_'+str(r)+'[63:63] = midSB_'+str(r)+'[63:63]);']
		constraints = constraints + ['ASSERT(AIs_'+str(r)+'[63:63] = AmidSB_'+str(r)+'[63:63]);']
		for i in range(63):
			constraints = constraints + ['ASSERT(Is_'+str(r)+'['+str(i*16%63)+':'+str(i*16%63)+'] = midSB_'+str(r)+'['+str(i)+':'+str(i)+']);']
			constraints = constraints + ['ASSERT(AIs_'+str(r)+'['+str(i*16%63)+':'+str(i*16%63)+'] = AmidSB_'+str(r)+'['+str(i)+':'+str(i)+']);']
			
		return constraints
		
	def genModel(self,P_in,C_out,begr,R):
		C = list([])
		
		for i in range(begr-1, begr+R):
			C = C + self.collectvariables(i)
		
		
		for i in range(begr, begr+R):
			C = C + self.genDiff_Pass(i)
		
		# C = C + ['ASSERT(Is_'+str(begr-1)+' /= AIs_'+str(begr-1)+');']
		
		# for i in range(int(self.blocksize/self.cellsize)):
		# 	if i == P_in[0]:
		# 		C = C + ['ASSERT(Is_'+str(begr-1)+'['+str(i*self.cellsize+3)+':'+str(i*self.cellsize)+'] /= 0x0);']
		# 	else:
		# 		C = C + ['ASSERT(Is_'+str(begr-1)+'['+str(i*self.cellsize+3)+':'+str(i*self.cellsize)+'] = 0x0);']
		# 	if i == P_in[1]:
		# 		C = C + ['ASSERT(AIs_'+str(begr-1)+'['+str(i*self.cellsize+3)+':'+str(i*self.cellsize)+'] /= 0x0);']
		# 	else:
		# 		C = C + ['ASSERT(AIs_'+str(begr-1)+'['+str(i*self.cellsize+3)+':'+str(i*self.cellsize)+'] = 0x0);']
		
		# for j in range(int(self.blocksize/self.cellsize)):
		# 	if j == C_out[0]:
		# 		C = C + ['ASSERT(midSB_'+str(begr+R-1)+'['+str(j*self.cellsize+3)+':'+str(j*self.cellsize)+'] /= 0x0);']
		# 	else:
		# 		C = C + ['ASSERT(midSB_'+str(begr+R-1)+'['+str(j*self.cellsize+3)+':'+str(j*self.cellsize)+'] = 0x0);']
		# 	if j == C_out[1]:
		# 		C = C + ['ASSERT(AmidSB_'+str(begr+R-1)+'['+str(j*self.cellsize+3)+':'+str(j*self.cellsize)+'] /= 0x0);']
		# 	else:
		# 		C = C + ['ASSERT(AmidSB_'+str(begr+R-1)+'['+str(j*self.cellsize+3)+':'+str(j*self.cellsize)+'] = 0x0);']
		
		# C = C + ['ASSERT(Is_'+str(begr-1)+'['+str(PD[0])+':'+str(PD[0])+']=0bin1);']
		# C = C + ['ASSERT(AIs_'+str(begr-1)+'['+str(PD[1])+':'+str(PD[1])+']=0bin1);']
		# C = C + ['ASSERT(Is_'+str(begr+R-1)+'['+str(CD[0])+':'+str(CD[0])+']=0bin1);']
		# C = C + ['ASSERT(AIs_'+str(begr+R-1)+'['+str(CD[1])+':'+str(CD[1])+']=0bin1);']
		
		# if PD[0]==0:
		# 	C = C + ['ASSERT(Is_'+str(begr-1)+'[63:'+str(PD[0]+1)+']=0bin'+'0'*63+');']
		# elif PD[0]==63:
		# 	C = C + ['ASSERT(Is_'+str(begr-1)+'['+str(PD[0]-1)+':0]=0bin'+'0'*63+');']
		# else:
		# 	C = C + ['ASSERT(Is_'+str(begr-1)+'[63:'+str(PD[0]+1)+']@Is_'+str(begr-1)+'['+str(PD[0]-1)+':0]=0bin'+'0'*63+');']

		# if PD[1]==0:
		# 	C = C + ['ASSERT(AIs_'+str(begr-1)+'[63:'+str(PD[1]+1)+']=0bin'+'0'*63+');']
		# elif PD[1]==63:
		# 	C = C + ['ASSERT(AIs_'+str(begr-1)+'['+str(PD[1]-1)+':0]=0bin'+'0'*63+');']
		# else:
		# 	C = C + ['ASSERT(AIs_'+str(begr-1)+'[63:'+str(PD[1]+1)+']@AIs_'+str(begr-1)+'['+str(PD[1]-1)+':0]=0bin'+'0'*63+');']

		# if CD[0]==0:
		# 	C = C + ['ASSERT(Is_'+str(begr+R-1)+'[63:'+str(CD[0]+1)+']=0bin'+'0'*63+');']
		# elif CD[0]==63:
		# 	C = C + ['ASSERT(Is_'+str(begr+R-1)+'['+str(CD[0]-1)+':0]=0bin'+'0'*63+');']
		# else:
		# 	C = C + ['ASSERT(Is_'+str(begr+R-1)+'[63:'+str(CD[0]+1)+']@Is_'+str(begr+R-1)+'['+str(CD[0]-1)+':0]=0bin'+'0'*63+');']

		# if CD[1]==0:
		# 	C = C + ['ASSERT(AIs_'+str(begr+R-1)+'[63:'+str(CD[1]+1)+']=0bin'+'0'*63+');']
		# elif CD[1]==63:
		# 	C = C + ['ASSERT(AIs_'+str(begr+R-1)+'['+str(CD[1]-1)+':0]=0bin'+'0'*63+');']
		# else:
		# 	C = C + ['ASSERT(AIs_'+str(begr+R-1)+'[63:'+str(CD[1]+1)+']@AIs_'+str(begr+R-1)+'['+str(CD[1]-1)+':0]=0bin'+'0'*63+');']
		
		hex_string_16 = '{:0%dx}' % 16
		C = C + ['ASSERT(Is_'+str(begr-1)+' = 0x'+hex_string_16.format(P_in[0])+');']
		C = C + ['ASSERT(AIs_'+str(begr-1)+' = 0x'+hex_string_16.format(P_in[1])+');']
		C = C + ['ASSERT(midSB_'+str(begr+R-1)+' = 0x'+hex_string_16.format(C_out[0])+');']
		C = C + ['ASSERT(AmidSB_'+str(begr+R-1)+' =  0x'+hex_string_16.format(C_out[1])+');']

		# add query
		C = C + ['QUERY(FALSE);']
		C = C + ['COUNTEREXAMPLE;']
		
		filename = 'PRESENT_normal_AND_2_leaves_ID.cvc'
		
		o = open(filename, 'w')
		for c in C:
			o.write(c)
			o.write('\n')
		o.close()

P_in = [int(sys.argv[1]),int(sys.argv[2])]
C_out = [int(sys.argv[3]),int(sys.argv[4])]	
begr = int(sys.argv[5])
r = int(sys.argv[6])	

blocksize,keysize = 64,80
m = get_PRESENT(blocksize,keysize,normal_SDDT,Sbox)
m.genModel(P_in,C_out,begr,r)
