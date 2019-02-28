% Matlab script to generate inputs to various test cases


% Both All Zeros Test Case
in = zeros(31, 128);
save('input0000.dat', 'in');


% Both All Ones Test Case
in = ones(31, 128);
save('input0001.dat', 'in');


% First Input All True, Second Input All False
in = zeros(31, 128);
n=1;
while n <= 31;
	in(n,1) = 1;
	n = n + 1;
end
save('input0002.dat', 'in');


% First Input All False, Second Input All True
in = zeros(31,128);
n=1;
while n <= 31;
	in(n,2) = 1;
	n = n + 1;
end
save('input0003.dat', 'in');


% First Input All True, Second Input Oscillating between false and true
in = zeros(31,128);
n=1;
while n <= 31;
	in(n,1) = 1;
	if mod(n,2) == 1;
		in(n,2) = 0;
	else
		in(n,2) = 1;
	end
	n = n + 1;
end
save('input0004.dat', 'in');


% First Input All True, Second Input Oscillating between true and false
in = zeros(31,128);
n=1;
while n <= 31;
	in(n,1) = 1;
	if mod(n,2) == 1;
		in(n,2) = 1;
	else
		in(n,2) = 0;
	end
	n = n + 1;
end
save('input0005.dat', 'in');



% First Input All False, Second Input Oscillating between false and true
in = zeros(31,128);
n=1;
while n <= 31;
	if mod(n,2) == 1;
		in(n,2) = 0;
	else
		in(n,2) = 1;
	end
	n = n + 1;
end
save('input0006.dat', 'in');



% First Input All False, Second Input Oscillating between true and false
in = zeros(31,128);
n=1;
while n <= 31;
	if mod(n,2) == 1;
		in(n,2) = 1;
	else
		in(n,2) = 0;
	end
	n = n + 1;
end
save('input0007.dat', 'in');



% First Input Oscillating between false and true, Second Input All True
in = zeros(31,128);
n=1;
while n <= 31;
	in(n,2) = 1;
	if mod(n,2) == 1;
		in(n,1) = 0;
	else
		in(n,1) = 1;
	end
	n = n + 1;
end
save('input0008.dat', 'in');



% First Input Oscillating between true and false, Second Input All True
in = zeros(31,128);
n=1;
while n <= 31;
	in(n,2) = 1;
	if mod(n,2) == 1;
		in(n,1) = 1;
	else
		in(n,1) = 0;
	end
	n = n + 1;
end
save('input0009.dat', 'in');



% First Input Oscillating between false and true, Second Input All False
in = zeros(31,128);
n=1;
while n <= 31;
	if mod(n,2) == 1;
		in(n,1) = 0;
	else
		in(n,1) = 1;
	end
	n = n + 1;
end
save('input0010.dat', 'in');



% First Input Oscillating between true and false, Second Input All False
in = zeros(31,128);
n=1;
while n <= 31;
	if mod(n,2) == 1;
		in(n,1) = 1;
	else
		in(n,1) = 0;
	end
	n = n + 1;
end
save('input0011.dat', 'in');



% First Input Five Time Step Pulse Wave, Second Input All True
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	in(n+1,2) =1;
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 0;
	else
		in(n+1,1) = 1;
	end
	n = n + 1;
end
save('input0012.dat', 'in');



% First Input Five Time Step Pulse Wave, Second Input All False
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 0;
	else
		in(n+1,1) = 1;
	end
	n = n + 1;
end
save('input0013.dat', 'in');



% First Input Five Time Step Inverse Pulse Wave, Second Input All True
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	in(n+1,2) =1;
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 1;
	else
		in(n+1,1) = 0;
	end
	n = n + 1;
end
save('input0014.dat', 'in');



% First Input Five Time Step Inverse Pulse Wave, Second Input All False
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 1;
	else
		in(n+1,1) = 0;
	end
	n = n + 1;
end
save('input0015.dat', 'in');



% First Input All True, Second Input Five Time Step Pulse Wave
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	in(n+1,1) =1;
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,2) = 0;
	else
		in(n+1,2) = 1;
	end
	n = n + 1;
end
save('input0016.dat', 'in');



% First Input All False, Second Input Five Time Step Pulse Wave
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,2) = 0;
	else
		in(n+1,2) = 1;
	end
	n = n + 1;
end
save('input0017.dat', 'in');



% First Input All True, Second Input Five Time Step Inverse Pulse Wave
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	in(n+1,1) =1;
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,2) = 1;
	else
		in(n+1,2) = 0;
	end
	n = n + 1;
end
save('input0018.dat', 'in');



% First Input All False, Second Input Five Time Step Inverse Pulse Wave
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,2) = 1;
	else
		in(n+1,2) = 0;
	end
	n = n + 1;
end
save('input0019.dat', 'in');




% Both Inputs are 5 time step pulse waves
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 0;
		in(n+1,2) = 0;
	else
		in(n+1,1) = 1;
		in(n+1,2) = 1;
	end
	n = n + 1;
end
save('input0020.dat', 'in');



% First Input 5 time step Pulse Wave. Second Input Inverse 5 time step pulse wave.
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 0;
		in(n+1,2) = 1;
	else
		in(n+1,1) = 1;
		in(n+1,2) = 0;
	end
	n = n + 1;
end
save('input0021.dat', 'in');



% First Input 5 time step Inverse Pulse Wave. Second Input 5 time step pulse wave.
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 1;
		in(n+1,2) = 0;
	else
		in(n+1,1) = 0;
		in(n+1,2) = 1;
	end
	n = n + 1;
end
save('input0022.dat', 'in');



% Both Inputs 5 Time Step Inverse Pulse Waves
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 1;
		in(n+1,2) = 1;
	else
		in(n+1,1) = 0;
		in(n+1,2) = 0;
	end
	n = n + 1;
end
save('input0023.dat', 'in');



% Both Inputs are five time step pulses, with the second input shifted right by 3
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 0;
	else
		in(n+1,1) = 1;
	end
	n = n + 1;
end

in(1,2)  = 0;
in(2,2)  = 0;
in(3,2)  = 0;
in(4,2)  = 0;
in(5,2)  = 0;
in(6,2)  = 0;
in(7,2)  = 0;
in(8,2)  = 0;
in(9,2)  = 1;
in(10,2) = 1;
in(11,2) = 1;
in(12,2) = 1;
in(13,2) = 1;
in(14,2) = 0;
in(15,2) = 0;
in(16,2) = 0;
in(17,2) = 0;
in(18,2) = 0;
in(19,2) = 1;
in(20,2) = 1;
in(21,2) = 1;
in(22,2) = 1;
in(23,2) = 1;
in(24,2) = 0;
in(25,2) = 0;
in(26,2) = 0;
in(27,2) = 0;
in(28,2) = 0;
in(29,2) = 1;
in(30,2) = 1;
in(31,2) = 1;
save('input0024.dat', 'in');


% Both Inputs are five time step pulses, with the second input shifted right by 3
% First Input Wave is inverse wave.
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 1;
	else
		in(n+1,1) = 0;
	end
	n = n + 1;
end

in(1,2)  = 0;
in(2,2)  = 0;
in(3,2)  = 0;
in(4,2)  = 0;
in(5,2)  = 0;
in(6,2)  = 0;
in(7,2)  = 0;
in(8,2)  = 0;
in(9,2)  = 1;
in(10,2) = 1;
in(11,2) = 1;
in(12,2) = 1;
in(13,2) = 1;
in(14,2) = 0;
in(15,2) = 0;
in(16,2) = 0;
in(17,2) = 0;
in(18,2) = 0;
in(19,2) = 1;
in(20,2) = 1;
in(21,2) = 1;
in(22,2) = 1;
in(23,2) = 1;
in(24,2) = 0;
in(25,2) = 0;
in(26,2) = 0;
in(27,2) = 0;
in(28,2) = 0;
in(29,2) = 1;
in(30,2) = 1;
in(31,2) = 1;
save('input0025.dat', 'in');



% Both Inputs are five time step pulses, with the second input shifted right by 3
%Second Wave is Inverse
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 0;
	else
		in(n+1,1) = 1;
	end
	n = n + 1;
end

in(1,2)  = 1;
in(2,2)  = 1;
in(3,2)  = 1;
in(4,2)  = 1;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 0;
in(10,2) = 0;
in(11,2) = 0;
in(12,2) = 0;
in(13,2) = 0;
in(14,2) = 1;
in(15,2) = 1;
in(16,2) = 1;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 0;
in(20,2) = 0;
in(21,2) = 0;
in(22,2) = 0;
in(23,2) = 0;
in(24,2) = 1;
in(25,2) = 1;
in(26,2) = 1;
in(27,2) = 1;
in(28,2) = 1;
in(29,2) = 0;
in(30,2) = 0;
in(31,2) = 0;
save('input0026.dat', 'in');



% Both Inputs are five time step pulses, with the second input shifted right by 3
% Second Wave is Inverse
% First Wave is Inverse
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,1) = 1;
	else
		in(n+1,1) = 0;
	end
	n = n + 1;
end

in(1,2)  = 1;
in(2,2)  = 1;
in(3,2)  = 1;
in(4,2)  = 1;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 0;
in(10,2) = 0;
in(11,2) = 0;
in(12,2) = 0;
in(13,2) = 0;
in(14,2) = 1;
in(15,2) = 1;
in(16,2) = 1;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 0;
in(20,2) = 0;
in(21,2) = 0;
in(22,2) = 0;
in(23,2) = 0;
in(24,2) = 1;
in(25,2) = 1;
in(26,2) = 1;
in(27,2) = 1;
in(28,2) = 1;
in(29,2) = 0;
in(30,2) = 0;
in(31,2) = 0;
save('input0027.dat', 'in');



% Both Inputs are five time step pulses, with the first input shifted right by 3
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,2) = 0;
	else
		in(n+1,2) = 1;
	end
	n = n + 1;
end
in(1,1)  = 0;
in(2,1)  = 0;
in(3,1)  = 0;
in(4,1)  = 0;
in(5,1)  = 0;
in(6,1)  = 0;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 1;
in(10,1) = 1;
in(11,1) = 1;
in(12,1) = 1;
in(13,1) = 1;
in(14,1) = 0;
in(15,1) = 0;
in(16,1) = 0;
in(17,1) = 0;
in(18,1) = 0;
in(19,1) = 1;
in(20,1) = 1;
in(21,1) = 1;
in(22,1) = 1;
in(23,1) = 1;
in(24,1) = 0;
in(25,1) = 0;
in(26,1) = 0;
in(27,1) = 0;
in(28,1) = 0;
in(29,1) = 1;
in(30,1) = 1;
in(31,1) = 1;
save('input0028.dat', 'in');



% Both Inputs are five time step pulses, with the first input shifted right by 3
% Second Input Inverse
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,2) = 1;
	else
		in(n+1,2) = 0;
	end
	n = n + 1;
end
in(1,1)  = 0;
in(2,1)  = 0;
in(3,1)  = 0;
in(4,1)  = 0;
in(5,1)  = 0;
in(6,1)  = 0;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 1;
in(10,1) = 1;
in(11,1) = 1;
in(12,1) = 1;
in(13,1) = 1;
in(14,1) = 0;
in(15,1) = 0;
in(16,1) = 0;
in(17,1) = 0;
in(18,1) = 0;
in(19,1) = 1;
in(20,1) = 1;
in(21,1) = 1;
in(22,1) = 1;
in(23,1) = 1;
in(24,1) = 0;
in(25,1) = 0;
in(26,1) = 0;
in(27,1) = 0;
in(28,1) = 0;
in(29,1) = 1;
in(30,1) = 1;
in(31,1) = 1;
save('input0029.dat', 'in');



% Both Inputs are five time step pulses, with the first input shifted right by 3
% First Input is Inverse
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,2) = 0;
	else
		in(n+1,2) = 1;
	end
	n = n + 1;
end
in(1,2)  = 1;
in(2,2)  = 1;
in(3,2)  = 1;
in(4,2)  = 1;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 0;
in(10,2) = 0;
in(11,2) = 0;
in(12,2) = 0;
in(13,2) = 0;
in(14,2) = 1;
in(15,2) = 1;
in(16,2) = 1;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 0;
in(20,2) = 0;
in(21,2) = 0;
in(22,2) = 0;
in(23,2) = 0;
in(24,2) = 1;
in(25,2) = 1;
in(26,2) = 1;
in(27,2) = 1;
in(28,2) = 1;
in(29,2) = 0;
in(30,2) = 0;
in(31,2) = 0;
save('input0030.dat', 'in');



% Both Inputs are five time step pulses, with the first input shifted right by 3
% Second Input is Inverse
% First Input is Inverse
in = zeros(31, 128);
n=0;
flip=1;
while n < 31
	if mod(n,5) == 0;
		flip = 1 - flip;
	end

	if flip == 0;
		in(n+1,2) = 1;
	else
		in(n+1,2) = 0;
	end
	n = n + 1;
end
in(1,2)  = 1;
in(2,2)  = 1;
in(3,2)  = 1;
in(4,2)  = 1;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 0;
in(10,2) = 0;
in(11,2) = 0;
in(12,2) = 0;
in(13,2) = 0;
in(14,2) = 1;
in(15,2) = 1;
in(16,2) = 1;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 0;
in(20,2) = 0;
in(21,2) = 0;
in(22,2) = 0;
in(23,2) = 0;
in(24,2) = 1;
in(25,2) = 1;
in(26,2) = 1;
in(27,2) = 1;
in(28,2) = 1;
in(29,2) = 0;
in(30,2) = 0;
in(31,2) = 0;
save('input0031.dat', 'in');



% Figure 4.39
in = zeros(10, 128);
in(1,1)  = 0;
in(2,1)  = 1;
in(3,1)  = 1;
in(4,1)  = 1;
in(5,1)  = 1;
in(6,1)  = 1;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 0;
in(10,1) = 0;
in(1,2)  = 0;
in(2,2)  = 0;
in(3,2)  = 0;
in(4,2)  = 0;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 1;
in(10,2) = 0;
save('input0032.dat', 'in');



% Example for TACAS14 Paper
in=zeros(31,128);

in(11:25,1) = 1;

in(4:11,2) = 1;
in(14,2) = 1;
in(16:19,2) = 1;
in(22:25,2) = 1;
in(27:29,2) = 1;
save('input0033.dat', 'in');



% test AND operation
in=zeros(31,128);
in(6:31,1) = 1;
in(4:31,2) = 1;
save('input0034.dat', 'in');



% First Input all True
% Second Input Increasing Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,1) =1;
	n = n + 1;
end
in(1,2)  = 0;
in(2,2)  = 1;
in(3,2)  = 0;
in(4,2)  = 1;
in(5,2)  = 0;
in(6,2)  = 0;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 0;
in(10,2) = 0;
in(11,2) = 1;
in(12,2) = 1;
in(13,2) = 0;
in(14,2) = 0;
in(15,2) = 0;
in(16,2) = 0;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 1;
in(20,2) = 1;
in(21,2) = 0;
in(22,2) = 0;
in(23,2) = 0;
in(24,2) = 0;
in(25,2) = 1;
in(26,2) = 1;
in(27,2) = 1;
in(28,2) = 1;
in(29,2) = 0;
in(30,2) = 0;
in(31,2) = 0;
save('input0035.dat', 'in');


% First Input all True
% Second Input Increasing Inverse Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,1) = 1;
	n = n + 1;
end
in(1,2)  = 1;
in(2,2)  = 0;
in(3,2)  = 1;
in(4,2)  = 0;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 0;
in(8,2)  = 0;
in(9,2)  = 1;
in(10,2) = 1;
in(11,2) = 0;
in(12,2) = 0;
in(13,2) = 1;
in(14,2) = 1;
in(15,2) = 1;
in(16,2) = 1;
in(17,2) = 0;
in(18,2) = 0;
in(19,2) = 0;
in(20,2) = 0;
in(21,2) = 1;
in(22,2) = 1;
in(23,2) = 1;
in(24,2) = 1;
in(25,2) = 0;
in(26,2) = 0;
in(27,2) = 0;
in(28,2) = 0;
in(29,2) = 1;
in(30,2) = 1;
in(31,2) = 1;
save('input0036.dat', 'in');



% First Input all False
% Second Input Increasing Pulse
in = zeros(31, 128);
in(1,2)  = 0;
in(2,2)  = 1;
in(3,2)  = 0;
in(4,2)  = 1;
in(5,2)  = 0;
in(6,2)  = 0;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 0;
in(10,2) = 0;
in(11,2) = 1;
in(12,2) = 1;
in(13,2) = 0;
in(14,2) = 0;
in(15,2) = 0;
in(16,2) = 0;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 1;
in(20,2) = 1;
in(21,2) = 0;
in(22,2) = 0;
in(23,2) = 0;
in(24,2) = 0;
in(25,2) = 1;
in(26,2) = 1;
in(27,2) = 1;
in(28,2) = 1;
in(29,2) = 0;
in(30,2) = 0;
in(31,2) = 0;
save('input0037.dat', 'in');



% First Input all False
% Second Input Increasing Inverse Pulse
in = zeros(31, 128);
in(1,2)  = 1;
in(2,2)  = 0;
in(3,2)  = 1;
in(4,2)  = 0;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 0;
in(8,2)  = 0;
in(9,2)  = 1;
in(10,2) = 1;
in(11,2) = 0;
in(12,2) = 0;
in(13,2) = 1;
in(14,2) = 1;
in(15,2) = 1;
in(16,2) = 1;
in(17,2) = 0;
in(18,2) = 0;
in(19,2) = 0;
in(20,2) = 0;
in(21,2) = 1;
in(22,2) = 1;
in(23,2) = 1;
in(24,2) = 1;
in(25,2) = 0;
in(26,2) = 0;
in(27,2) = 0;
in(28,2) = 0;
in(29,2) = 1;
in(30,2) = 1;
in(31,2) = 1;
save('input0038.dat', 'in');



% Second Input all True
% First Input Increasing Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,2) =1;
	n = n + 1;
end
in(1,1)  = 0;
in(2,1)  = 1;
in(3,1)  = 0;
in(4,1)  = 1;
in(5,1)  = 0;
in(6,1)  = 0;
in(7,1)  = 1;
in(8,1)  = 1;
in(9,1)  = 0;
in(10,1) = 0;
in(11,1) = 1;
in(12,1) = 1;
in(13,1) = 0;
in(14,1) = 0;
in(15,1) = 0;
in(16,1) = 0;
in(17,1) = 1;
in(18,1) = 1;
in(19,1) = 1;
in(20,1) = 1;
in(21,1) = 0;
in(22,1) = 0;
in(23,1) = 0;
in(24,1) = 0;
in(25,1) = 1;
in(26,1) = 1;
in(27,1) = 1;
in(28,1) = 1;
in(29,1) = 0;
in(30,1) = 0;
in(31,1) = 0;
save('input0039.dat', 'in');



% Second Input all True
% First Input Increasing Inverse Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,2) = 1;
	n = n + 1;
end
in(1,1)  = 1;
in(2,1)  = 0;
in(3,1)  = 1;
in(4,1)  = 0;
in(5,1)  = 1;
in(6,1)  = 1;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 1;
in(10,1) = 1;
in(11,1) = 0;
in(12,1) = 0;
in(13,1) = 1;
in(14,1) = 1;
in(15,1) = 1;
in(16,1) = 1;
in(17,1) = 0;
in(18,1) = 0;
in(19,1) = 0;
in(20,1) = 0;
in(21,1) = 1;
in(22,1) = 1;
in(23,1) = 1;
in(24,1) = 1;
in(25,1) = 0;
in(26,1) = 0;
in(27,1) = 0;
in(28,1) = 0;
in(29,1) = 1;
in(30,1) = 1;
in(31,1) = 1;
save('input0040.dat', 'in');



% Second Input all False
% First Input Increasing Pulse
in = zeros(31, 128);
in(1,1)  = 0;
in(2,1)  = 1;
in(3,1)  = 0;
in(4,1)  = 1;
in(5,1)  = 0;
in(6,1)  = 0;
in(7,1)  = 1;
in(8,1)  = 1;
in(9,1)  = 0;
in(10,1) = 0;
in(11,1) = 1;
in(12,1) = 1;
in(13,1) = 0;
in(14,1) = 0;
in(15,1) = 0;
in(16,1) = 0;
in(17,1) = 1;
in(18,1) = 1;
in(19,1) = 1;
in(20,1) = 1;
in(21,1) = 0;
in(22,1) = 0;
in(23,1) = 0;
in(24,1) = 0;
in(25,1) = 1;
in(26,1) = 1;
in(27,1) = 1;
in(28,1) = 1;
in(29,1) = 0;
in(30,1) = 0;
in(31,1) = 0;
save('input0041.dat', 'in');



% Second Input all False
% First Input Increasing Inverse Pulse
in = zeros(31, 128);
in(1,1)  = 1;
in(2,1)  = 0;
in(3,1)  = 1;
in(4,1)  = 0;
in(5,1)  = 1;
in(6,1)  = 1;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 1;
in(10,1) = 1;
in(11,1) = 0;
in(12,1) = 0;
in(13,1) = 1;
in(14,1) = 1;
in(15,1) = 1;
in(16,1) = 1;
in(17,1) = 0;
in(18,1) = 0;
in(19,1) = 0;
in(20,1) = 0;
in(21,1) = 1;
in(22,1) = 1;
in(23,1) = 1;
in(24,1) = 1;
in(25,1) = 0;
in(26,1) = 0;
in(27,1) = 0;
in(28,1) = 0;
in(29,1) = 1;
in(30,1) = 1;
in(31,1) = 1;
save('input0042.dat', 'in');



% First Input all True
% Second Input Decreasing Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,1) = 1;
	n = n + 1;
end
in(1,2)  = 0;
in(2,2)  = 0;
in(3,2)  = 0;
in(4,2)  = 0;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 0;
in(10,2) = 0;
in(11,2) = 0;
in(12,2) = 0;
in(13,2) = 1;
in(14,2) = 1;
in(15,2) = 1;
in(16,2) = 1;
in(17,2) = 0;
in(18,2) = 0;
in(19,2) = 1;
in(20,2) = 1;
in(21,2) = 0;
in(22,2) = 0;
in(23,2) = 1;
in(24,2) = 1;
in(25,2) = 0;
in(26,2) = 1;
in(27,2) = 0;
in(28,2) = 1;
in(29,2) = 0;
in(30,2) = 1;
in(31,2) = 0;
save('input0043.dat', 'in');



% First Input all True
% Second Input Decreasing Inverse Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,1) = 1;
	n = n + 1;
end
in(1,2)  = 1;
in(2,2)  = 1;
in(3,2)  = 1;
in(4,2)  = 1;
in(5,2)  = 0;
in(6,2)  = 0;
in(7,2)  = 0;
in(8,2)  = 0;
in(9,2)  = 1;
in(10,2) = 1;
in(11,2) = 1;
in(12,2) = 1;
in(13,2) = 0;
in(14,2) = 0;
in(15,2) = 0;
in(16,2) = 0;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 0;
in(20,2) = 0;
in(21,2) = 1;
in(22,2) = 1;
in(23,2) = 0;
in(24,2) = 0;
in(25,2) = 1;
in(26,2) = 0;
in(27,2) = 1;
in(28,2) = 0;
in(29,2) = 1;
in(30,2) = 0;
in(31,2) = 1;
save('input0044.dat', 'in');



% First Input all False
% Second Input Decreasing Pulse
in = zeros(31, 128);
in(1,2)  = 0;
in(2,2)  = 0;
in(3,2)  = 0;
in(4,2)  = 0;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 0;
in(10,2) = 0;
in(11,2) = 0;
in(12,2) = 0;
in(13,2) = 1;
in(14,2) = 1;
in(15,2) = 1;
in(16,2) = 1;
in(17,2) = 0;
in(18,2) = 0;
in(19,2) = 1;
in(20,2) = 1;
in(21,2) = 0;
in(22,2) = 0;
in(23,2) = 1;
in(24,2) = 1;
in(25,2) = 0;
in(26,2) = 1;
in(27,2) = 0;
in(28,2) = 1;
in(29,2) = 0;
in(30,2) = 1;
in(31,2) = 0;
save('input0045.dat', 'in');



% First Input all False
% Second Input Decreasing Inverse Pulse
in = zeros(31, 128);
in(1,2)  = 1;
in(2,2)  = 1;
in(3,2)  = 1;
in(4,2)  = 1;
in(5,2)  = 0;
in(6,2)  = 0;
in(7,2)  = 0;
in(8,2)  = 0;
in(9,2)  = 1;
in(10,2) = 1;
in(11,2) = 1;
in(12,2) = 1;
in(13,2) = 0;
in(14,2) = 0;
in(15,2) = 0;
in(16,2) = 0;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 0;
in(20,2) = 0;
in(21,2) = 1;
in(22,2) = 1;
in(23,2) = 0;
in(24,2) = 0;
in(25,2) = 1;
in(26,2) = 0;
in(27,2) = 1;
in(28,2) = 0;
in(29,2) = 1;
in(30,2) = 0;
in(31,2) = 1;
save('input0046.dat', 'in');



% Second Input all True
% First Input Decreasing Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,2) = 1;
	n = n + 1;
end
in(1,1)  = 0;
in(2,1)  = 0;
in(3,1)  = 0;
in(4,1)  = 0;
in(5,1)  = 1;
in(6,1)  = 1;
in(7,1)  = 1;
in(8,1)  = 1;
in(9,1)  = 0;
in(10,1) = 0;
in(11,1) = 0;
in(12,1) = 0;
in(13,1) = 1;
in(14,1) = 1;
in(15,1) = 1;
in(16,1) = 1;
in(17,1) = 0;
in(18,1) = 0;
in(19,1) = 1;
in(20,1) = 1;
in(21,1) = 0;
in(22,1) = 0;
in(23,1) = 1;
in(24,1) = 1;
in(25,1) = 0;
in(26,1) = 1;
in(27,1) = 0;
in(28,1) = 1;
in(29,1) = 0;
in(30,1) = 1;
in(31,1) = 0;
save('input0047.dat', 'in');



% Second Input all True
% First Input Decreasing Inverse Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,2) = 1;
	n = n + 1;
end
in(1,1)  = 1;
in(2,1)  = 1;
in(3,1)  = 1;
in(4,1)  = 1;
in(5,1)  = 0;
in(6,1)  = 0;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 1;
in(10,1) = 1;
in(11,1) = 1;
in(12,1) = 1;
in(13,1) = 0;
in(14,1) = 0;
in(15,1) = 0;
in(16,1) = 0;
in(17,1) = 1;
in(18,1) = 1;
in(19,1) = 0;
in(20,1) = 0;
in(21,1) = 1;
in(22,1) = 1;
in(23,1) = 0;
in(24,1) = 0;
in(25,1) = 1;
in(26,1) = 0;
in(27,1) = 1;
in(28,1) = 0;
in(29,1) = 1;
in(30,1) = 0;
in(31,1) = 1;
save('input0048.dat', 'in');



% Second Input all False
% First Input Decreasing Pulse
in = zeros(31, 128);
in(1,1)  = 0;
in(2,1)  = 0;
in(3,1)  = 0;
in(4,1)  = 0;
in(5,1)  = 1;
in(6,1)  = 1;
in(7,1)  = 1;
in(8,1)  = 1;
in(9,1)  = 0;
in(10,1) = 0;
in(11,1) = 0;
in(12,1) = 0;
in(13,1) = 1;
in(14,1) = 1;
in(15,1) = 1;
in(16,1) = 1;
in(17,1) = 0;
in(18,1) = 0;
in(19,1) = 1;
in(20,1) = 1;
in(21,1) = 0;
in(22,1) = 0;
in(23,1) = 1;
in(24,1) = 1;
in(25,1) = 0;
in(26,1) = 1;
in(27,1) = 0;
in(28,1) = 1;
in(29,1) = 0;
in(30,1) = 1;
in(31,1) = 0;
save('input0049.dat', 'in');



% Second Input all False
% First Input Decreasing Inverse Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,2) = 1;
	n = n + 1;
end
in(1,1)  = 1;
in(2,1)  = 1;
in(3,1)  = 1;
in(4,1)  = 1;
in(5,1)  = 0;
in(6,1)  = 0;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 1;
in(10,1) = 1;
in(11,1) = 1;
in(12,1) = 1;
in(13,1) = 0;
in(14,1) = 0;
in(15,1) = 0;
in(16,1) = 0;
in(17,1) = 1;
in(18,1) = 1;
in(19,1) = 0;
in(20,1) = 0;
in(21,1) = 1;
in(22,1) = 1;
in(23,1) = 0;
in(24,1) = 0;
in(25,1) = 1;
in(26,1) = 0;
in(27,1) = 1;
in(28,1) = 0;
in(29,1) = 1;
in(30,1) = 0;
in(31,1) = 1;
save('input0050.dat', 'in');






% Second Input all True
% First Input Decreasing Inverse Pulse
in = zeros(31, 128);
n=0;
while n < 31
	in(n+1,2) = 1;
	n = n + 1;
end

in(1,1)  = 1;
in(2,1)  = 0;
in(3,1)  = 0;
in(4,1)  = 0;
in(5,1)  = 0;
in(6,1)  = 0;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 0;
in(10,1) = 0;
in(11,1) = 0;
in(12,1) = 0;
in(13,1) = 0;
in(14,1) = 0;
in(15,1) = 0;
in(16,1) = 0;
in(17,1) = 0;
in(18,1) = 0;
in(19,1) = 0;
in(20,1) = 0;
in(21,1) = 0;
in(22,1) = 0;
in(23,1) = 0;
in(24,1) = 0;
in(25,1) = 0;
in(26,1) = 0;
in(27,1) = 0;
in(28,1) = 0;
in(29,1) = 0;
in(30,1) = 0;
in(31,1) = 0;
save('input0051.dat', 'in');


% Pei Test Input
in = zeros(39, 128);
in(1,1)  = 0;
in(2,1)  = 0;
in(3,1)  = 0;
in(4,1)  = 0;
in(5,1)  = 0;
in(6,1)  = 0;
in(7,1)  = 0;
in(8,1)  = 0;
in(9,1)  = 0;
in(10,1) = 0;
in(11,1) = 1;
in(12,1) = 1;
in(13,1) = 1;
in(14,1) = 1;
in(15,1) = 1;
in(16,1) = 1;
in(17,1) = 1;
in(18,1) = 1;
in(19,1) = 1;
in(20,1) = 1;
in(21,1) = 1;
in(22,1) = 1;
in(23,1) = 1;
in(24,1) = 1;
in(25,1) = 1;
in(26,1) = 0;
in(27,1) = 0;
in(28,1) = 0;
in(29,1) = 0;
in(30,1) = 0;
in(31,1) = 0;
in(32,1) = 1;
in(33,1) = 1;
in(34,1) = 1;
in(35,1) = 1;
in(36,1) = 1;
in(37,1) = 1;
in(38,1) = 1;
in(39,1) = 1;


in(1,2)  = 0;
in(2,2)  = 0;
in(3,2)  = 0;
in(4,2)  = 1;
in(5,2)  = 1;
in(6,2)  = 1;
in(7,2)  = 1;
in(8,2)  = 1;
in(9,2)  = 1;
in(10,2) = 1;
in(11,2) = 1;
in(12,2) = 0;
in(13,2) = 0;
in(14,2) = 1;
in(15,2) = 0;
in(16,2) = 1;
in(17,2) = 1;
in(18,2) = 1;
in(19,2) = 1;
in(20,2) = 0;
in(21,2) = 0;
in(22,2) = 1;
in(23,2) = 1;
in(24,2) = 1;
in(25,2) = 1;
in(26,2) = 0;
in(27,2) = 1;
in(28,2) = 1;
in(29,2) = 1;
in(30,2) = 0;
in(31,2) = 0;
in(32,2) = 1;
in(33,2) = 1;
in(34,2) = 1;
in(35,2) = 1;
in(36,2) = 1;
in(37,2) = 1;
in(38,2) = 1;
in(39,2) = 1;
save('tacas.dat', 'in');
