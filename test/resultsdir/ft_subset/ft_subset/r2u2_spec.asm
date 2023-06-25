[95mBZ Assembly[0m:
	b0 load s0 a0
	b1 load s0 a1
	b2 load s1 a2
	b3 load s1 a3
	b4 load s0 a4
	b5 load s1 a5
	b6 load s0 a6
	b7 load s0 a7
	b8 load s1 a8
	b9 load s0 a9
	b10 load s1 a10
	b11 load s1 a11
	b12 load s0 a12
	b13 load s1 a13
	b14 load s0 a14
	b15 load s1 a15
	b16 load s0 a16
	b17 load s1 a17
	b18 load s0 a18
[95mFT Assembly[0m:
	n0 load a0
	n1 not n0 
	n2 end n1 f0
	n3 load a1
	n4 not n3 
	n5 not n4 
	n6 end n5 f1
	n7 load a2
	n8 global n7 0 5
	n9 end n8 f2
	n10 load a3
	n11 not n10 
	n12 global n11 0 2
	n13 not n12 
	n14 end n13 f3
	n15 load a4
	n16 global n15 0 2
	n17 load a5
	n18 and n16 n17 
	n19 end n18 f4
	n20 load a6
	n21 global n20 5 10
	n22 end n21 f5
	n23 load a7
	n24 global n23 5 10
	n25 load a8
	n26 global n25 0 2
	n27 and n24 n26 
	n28 not n27 
	n29 end n28 f6
	n30 load a9
	n31 not n30 
	n32 not n31 
	n33 global n32 0 2
	n34 load a10
	n35 and n33 n34 
	n36 end n35 f7
	n37 load a11
	n38 load a12
	n39 global n38 0 8
	n40 and n37 n39 
	n41 end n40 f8
	n42 load a13
	n43 global n42 0 2
	n44 load a14
	n45 global n44 5 10
	n46 and n43 n45 
	n47 end n46 f9
	n48 load a15
	n49 global n48 0 2
	n50 end n49 f10
	n51 load a16
	n52 load a17
	n53 and n51 n52 
	n54 load a18
	n55 global n54 3 5
	n56 and n53 n55 
	n57 end n56 f11
	n58 endsequence
[95mPT Assembly[0m:
	n0 endsequence
[95mSCQ Assembly[0m:
	(0, 3)
	(3, 6)
	(6, 7)
	(7, 10)
	(10, 13)
	(13, 16)
	(16, 17)
	(17, 20)
	(20, 23)
	(23, 24)
	(24, 27)
	(27, 30)
	(30, 33)
	(33, 36)
	(36, 37)
	(37, 40)
	(40, 43)
	(43, 48)
	(48, 51)
	(51, 52)
	(52, 55)
	(55, 58)
	(58, 59)
	(59, 62)
	(62, 65)
	(65, 68)
	(68, 81)
	(81, 84)
	(84, 87)
	(87, 88)
	(88, 91)
	(91, 94)
	(94, 97)
	(97, 100)
	(100, 105)
	(105, 108)
	(108, 109)
	(109, 120)
	(120, 123)
	(123, 126)
	(126, 129)
	(129, 130)
	(130, 133)
	(133, 146)
	(146, 149)
	(149, 152)
	(152, 155)
	(155, 156)
	(156, 159)
	(159, 162)
	(162, 163)
	(163, 166)
	(166, 169)
	(169, 177)
	(177, 180)
	(180, 183)
	(183, 186)
	(186, 187)
[95mAliases[0m:
	F  0
	F  1
	F  2
	F  3
	F  4
	F  5
	F  6
	F  7
	F  8
	F  9
	F  10
	F  11
