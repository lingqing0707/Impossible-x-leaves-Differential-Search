import numpy as np
import sys

Sbox = [0x1, 0xa, 0x4, 0xc, 0x6, 0xf, 0x3, 0x9, 0x2, 0xd, 0xb, 0x7, 0x5, 0x0, 0x8, 0xe]
P = [0, 17, 34, 51, 48, 1, 18, 35, 32, 49, 2, 19, 16, 33, 50, 3, 4, 21, 38, 55, 52, 5, 22, 39, 36, 53, 6, 23, 20, 37, 54, 7, 8, 25, 42, 59, 56, 9, 26, 43, 40, 57, 10, 27, 24, 41, 58, 11, 12, 29, 46, 63, 60, 13, 30, 47, 44, 61, 14, 31, 28, 45, 62, 15]

def get_constraints_for_normal_SDDT(S):
	hex_string = '0x{:0%dx}' % 2
	constraints = list([])
	#constraints = constraints + ['input_diff, output_diff: BITVECTOR(4);']
	a = 'ASSERT( ( (input_diff=0x00) <=> (output_diff=0x00) ) '
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
	a = 'ASSERT( ( (input_value_diff[7:0]=0x00) <=> (output_diff=0x00)) '
	for x in range(len(S)):
		for alpha in range(1,len(S)*len(S)):
			beta = (S[x] ^ S[x ^ int(alpha/len(S))]) * len(S) + (S[x] ^ S[x ^ int(alpha%len(S))])
			a = a + 'AND ((input_value_diff='+hex_string_x.format(x)+'@'+hex_string.format(alpha)+') => (output_diff='+hex_string.format(beta)+')) '

	a = a + ');'
	return a
		
key_SDDT = get_constraints_for_key_SDDT(Sbox)
#print(SDDT)

class get_GIFT():
	def __init__(self,blocksize,keysize,SDDT,Sbox):
		self.blocksize = blocksize
		self.cellsize = int(blocksize / 16)
		self.Rounds = 31
		self.keysize = keysize
		self.SDDT = SDDT
		self.P = P
		self.Sbox = Sbox
	
	def genSbox(self):
		constraints = list([])
		constraints = constraints + ['%declare Sbox function']
		constraints = constraints + ['SS : ARRAY BITVECTOR(' + str(self.cellsize) + ') OF BITVECTOR(' + str(self.cellsize) + ');']
		bit_string = '{:0%db}' % self.cellsize
		for i in range(0, 2**self.cellsize):
			i_ = bit_string.format(i)
			j_ = bit_string.format(self.Sbox[i])
			constraints = constraints +  ['ASSERT(SS[0bin%s] = 0bin%s);'%(i_, j_)]
		return constraints
		
	def collectkeys(self,begr,r):
		constraints = list([])
		bit_string = '{:0%db}' % 5
		constraints = constraints + ['%generate keys']
		constraints = constraints + ['MK_'+str(begr-1)+': BITVECTOR('+str(keysize)+');']
		for r in range(begr-1, begr+r-1):
			constraints = constraints + ['SK_'+str(r)+':BITVECTOR('+str(int(self.blocksize/2))+');']
			constraints = constraints + ['ASSERT(SK_'+str(r)+' = MK_'+str(r)+'['+str(int(self.blocksize/2)-1)+':0]);']
			constraints = constraints + ['MK_'+str(r+1)+': BITVECTOR('+str(self.keysize)+');']
			constraints = constraints + ['ASSERT(MK_'+str(r+1)+'= MK_'+str(r)+'[17:16]@MK_'+str(r)+'[31:18]@MK_'+str(r)+'[11:0]@MK_'+str(r)+'[15:12]@MK_'+str(r)+'['+str(self.keysize-1)+':32]);']
			
		return constraints
		
	def collectvariables(self,r):
		constraints = list([])
		constraints = constraints + ['%declare r-th varibales']
		constraints = constraints + ['Is_'+str(r)+':BITVECTOR('+str(self.blocksize)+');']
		constraints = constraints + ['AIs_'+str(r)+':BITVECTOR('+str(self.blocksize)+');']
		constraints = constraints + ['Is_value_'+str(r)+':BITVECTOR('+str(self.blocksize)+');']
		return constraints
		
	def collectconstants(self,begr,r):
		constraints = list([])
		bit_string = '{:0%db}' % 5
		constraints = constraints + ['%generate Cons']
		constraints = constraints + ['Cons_'+str(begr-1)+': BITVECTOR(6);']
		for r in range(begr-1, begr+r-1):
			constraints = constraints + ['Cons_'+str(r+1)+':BITVECTOR(6);']
			constraints = constraints + ['ASSERT(Cons_'+str(r+1)+'= Cons_'+str(r)+'[4:0]@BVXOR(0b1,BVXOR(Cons_'+str(r)+'[5:5],Cons_'+str(r)+'[4:4])));']
			
		return constraints
		
	def genDiff_Pass(self,r):
		assert r >=1
		constraints = list([])
		
		constraints = constraints + ['%r-th encryption']
		constraints = constraints + ['midSB_value_'+str(r-1)+':BITVECTOR('+str(self.blocksize)+');']
		
		for i in range(16):
			constraints = constraints + ['ASSERT(midSB_value_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+'] = SS[Is_value_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+']]);']
		
		cc = [3,7,11,15,19,23]
		
		for i in range(64):
			if (i % 4) == 0:
				constraints = constraints + ['ASSERT(Is_value_'+str(r)+'['+str(i)+':'+str(i)+'] = BVXOR(midSB_value_'+str(r-1)+'['+str(self.P.index(i))+':'+str(self.P.index(i))+'], SK_'+str(r-1)+'['+str(int(i/4))+':'+str(int(i/4))+']));']
	
			elif (i % 4) == 1:
				constraints = constraints + ['ASSERT(Is_value_'+str(r)+'['+str(i)+':'+str(i)+'] = BVXOR(midSB_value_'+str(r-1)+'['+str(self.P.index(i))+':'+str(self.P.index(i))+'], SK_'+str(r-1)+'['+str(int(i/4)+16)+':'+str(int(i/4)+16)+']));']
				
			elif i in cc:
				constraints = constraints + ['ASSERT(Is_value_'+str(r)+'['+str(i)+':'+str(i)+'] = BVXOR(midSB_value_'+str(r-1)+'['+str(self.P.index(i))+':'+str(self.P.index(i))+'], Cons_'+str(r-1)+'['+str(cc.index(i))+':'+str(cc.index(i))+']));']
				
			elif i == (self.blocksize -1):
				constraints = constraints + ['ASSERT(Is_value_'+str(r)+'['+str(i)+':'+str(i)+'] = BVXOR(midSB_value_'+str(r-1)+'['+str(self.P.index(i))+':'+str(self.P.index(i))+'], 0bin1));']
	
			else:
				constraints = constraints + ['ASSERT(Is_value_'+str(r)+'['+str(i)+':'+str(i)+'] = midSB_value_'+str(r-1)+'['+str(self.P.index(i))+':'+str(self.P.index(i))+']);']
			
		
		constraints = constraints + ['%r-th Diff_Passption']
		constraints = constraints + ['midSB_'+str(r)+',AmidSB_'+str(r)+' :BITVECTOR('+str(self.blocksize)+');']
		
		for i in range(16):
			constraints = constraints + [self.SDDT.replace('input_value_diff[7:0]','Is_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+']@AIs_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+']').replace('input_value_diff', 'Is_value_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+']@Is_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+']@AIs_'+str(r-1)+'['+str(i*4+3)+':'+str(i*4)+']').replace('output_diff', 'midSB_'+str(r)+'['+str(i*4+3)+':'+str(i*4)+']@AmidSB_'+str(r)+'['+str(i*4+3)+':'+str(i*4)+']')]
			
		for i in range(64):
			constraints = constraints + ['ASSERT(Is_'+str(r)+'['+str(i)+':'+str(i)+'] = midSB_'+str(r)+'['+str(self.P.index(i))+':'+str(self.P.index(i))+']);']
			constraints = constraints + ['ASSERT(AIs_'+str(r)+'['+str(i)+':'+str(i)+'] = AmidSB_'+str(r)+'['+str(self.P.index(i))+':'+str(self.P.index(i))+']);']
		
		return constraints
		
	def genModel(self, begr, R, P_in, C_out, value_in, value_out):
		C = list([])
		d = self.genSbox()
		C = C + d
		
		for i in range(begr-1, begr+R):
			C = C + self.collectvariables(i)
		
		C = C + self.collectkeys(begr,r)
		C = C + self.collectconstants(begr,r)
		for i in range(begr, begr+R):
			C = C + self.genDiff_Pass(i)
		#C = C + ['ASSERT(Cons_0 = 0b000001);']


		hex_string_1 = '{:0%dx}' % 1
		C = C + ['ASSERT(Is_'+str(begr-1)+' = 0x000000000000000'+hex_string_1.format(P_in[0])+');']
		C = C + ['ASSERT(AIs_'+str(begr-1)+' = 0x000000000000000'+hex_string_1.format(P_in[1])+');']
		C = C + ['ASSERT(midSB_'+str(begr+R-1)+' = 0x000000000000000'+hex_string_1.format(C_out[0])+');']
		C = C + ['ASSERT(AmidSB_'+str(begr+R-1)+' =  0x000000000000000'+hex_string_1.format(C_out[1])+');']

		C = C + ['ASSERT(Is_value_'+str(begr-1)+'[3:0] = 0x'+hex_string_1.format(value_in)+');']
		C = C + ['ASSERT(midSB_value_'+str(begr+R-2)+'[3:0] = 0x'+hex_string_1.format(value_out)+');']

		# add query
		C = C + ['QUERY(FALSE);']
		C = C + ['COUNTEREXAMPLE;']
		
		filename = 'GIFT_AND_key_x_leaves_DC_SET.cvc'
		
		o = open(filename, 'w')
		for c in C:
			o.write(c)
			o.write('\n')
		o.close()

begr = int(sys.argv[1])
r = int(sys.argv[2])
P_in = [int(sys.argv[3]),int(sys.argv[4])]
C_out = [int(sys.argv[5]),int(sys.argv[6])]
value_in = int(sys.argv[7])
value_out = int(sys.argv[8])
blocksize,keysize = 64,128
m = get_GIFT(blocksize,keysize,key_SDDT,Sbox)
m.genModel(begr, r, P_in, C_out, value_in, value_out)
	





