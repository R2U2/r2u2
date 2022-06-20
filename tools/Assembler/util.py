def toBinary(value, width):
	# Try for an integer (Chris)
	try:
		value = int(value)

		# Handle sign
		if value < 0:
			# Convert to 2's complement
			value += 1
			b = bin(value)[3:]

			# Flip bits
			tmp = ''
			for digit in b:
				if digit == '0':
					tmp += '1'
				else:
					tmp += '0'
			b = tmp

			# Pad with 1s
			while len(b) < width:
				b = '1' + b
		else:
			b = bin(value)[2:]
			while len(b) < width:
				b = '0' + b

		if len(b) > width:
			print(value, "Error: does not fit into ", width, " bits")
			b = b[0:width]

		return b

	# If not an integer, try float
	except ValueError:
		# Sources for Code:
		# https://www.geeksforgeeks.org/python-program-to-convert-floating-to-binary/
		# https://www.geeksforgeeks.org/ieee-standard-754-floating-point-numbers/

		# set up constants for widths
		if(width == 32):
			bias = 127
			exp_width = 8
			mantissa_width = 23
		if(width == 64):
			bias = 1023
			exp_width = 11
			mantissa_width = 52

		value = float(value)

		# sign of the float
		if(value < 0):
			sign = '1'
			value = value*-1
		else:
			sign = '0'

		# write in base 2 scientific notation
		exp = 0
		while(not( 1 <= value and value < 2)):
			if(value < 1):
				value *= 2
				exp -= 1
			elif(value >= 2):
				value /= 2
				exp += 1

		# put exp into binary
		exp = bin(exp + bias)
		exp = exp[2:len(exp)]
		# if too short, pad with zeros at start
		while(len(exp) < exp_width):
			exp = '0' + exp
		# if too long, take most significant bits
		if(len(exp) > exp_width):
			exp = exp[0:exp_width]

		value -= 1
		#approximate the fraction
		mantissa = ''
		for val in range(0, mantissa_width):
			if(str(value) == '0'):
				mantissa += 0
			elif(str(value) == '1'):
				mantissa += '1'
				value = 0
			else:
				while(value > 1):
					value /= 10
				value *= 2
				w, d = str(value).split('.')
				mantissa += w
				value = float(d)

		return sign+exp+mantissa
