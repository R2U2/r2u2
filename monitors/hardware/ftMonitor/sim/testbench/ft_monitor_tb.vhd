-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : ft_monitor_tb.vhd
-- Author     : Patrick Moosbrugger (p.moosbrugger@gmail.com)
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: testbench for the ft_monitor
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
--use ieee.std_logic_unsigned.all;
use work.ft_monitor_pkg.all;
use work.log_input_pkg.all;

use work.testbench_util_pkg.all;
use std.textio.all;
--use work.cevrvu_top_pkg.all;
--library modelsim_lib;
--use modelsim_lib.util.all;
use work.math_pkg.all;

entity ft_monitor_tb is
  generic (
    imemFilePath   : string := "PATH_TO_DIRECTORY/r2u2/tools/preprocessing/tmp.ftm";    
    intFilePath    : string := "PATH_TO_DIRECTORY/r2u2/tools/preprocessing/tmp.fti";
	scqFilePath    : string := "PATH_TO_DIRECTORY/r2u2/tools/preprocessing/tmp.ftscq";
    inputFilePath  : string := "PATH_TO_DIRECTORY/r2u2/test/Inputs/atomic.trc.txt";
    outputFilePath : string := "PATH_TO_DIRECTORY/r2u2/test/R2U2.log"
    );
end entity;

architecture sim of ft_monitor_tb is
	constant CLK_FREQ                   : integer                                         := 100000000;
	constant SUT_FREQ                   : integer                                         := 100000;
	signal   s_clk, s_reset_n           : std_logic                                       := '0';
	signal   s_sutclk                   : std_logic                                       := '0';
	signal   s_rtc_timestamp            : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0)    := (others => '0');
	signal   s_atomics                  : std_logic_vector(ATOMICS_WIDTH-1 downto 0)      := (others => '0');
	signal   s_programming_stop         : boolean                                         := false;
	signal   stop                       : boolean                                         := false;
	signal   s_programming_imem         : std_logic                                       := '0';
	signal   s_programming_interval_mem : std_logic                                       := '0';
	signal   s_en                       : std_logic                                       := '0';
	signal   s_trigger                  : std_logic                                       := '0';
	signal   s_programming_memory_addr  : std_logic_vector(MEMBUS_ADDR_WIDTH-1 downto 0)  := (others => '0');
--	signal   s_programming_memory_data  : std_logic_vector (2*TIMESTAMP_WIDTH-1 downto 0) := (others => '0');
	signal   s_programming_memory_data  : std_logic_vector (MEMBUS_DATA_WIDTH-1 downto 0) := (others => '0');
	signal   s_violated                 : std_logic                                       := '0';
	signal   s_violated_valid           : std_logic                                       := '0';
	file mumonProgram_file              : text open read_mode is imemFilePath;
	file mumonInterval_file             : text open read_mode is intFilePath;
	file mumonSCQ_File                  : text open read_mode is scqFilePath;
	file testSample_file                : text open read_mode is inputFilePath;
	file testSampleResult_file          : text open write_mode is outputFilePath;
	signal   s_rtc_en                   : std_logic                                       := '0';

	-- spy signals
	signal new_result_spy	: std_logic;
	signal result_time_spy : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);

	--write output signal
	signal s_debug : debug_t;

	-- Reverse the order of a standard logic vector
	function reverse(input : std_logic_vector) return std_logic_vector is
		variable output : std_logic_vector(input'length - 1 downto 0);
	begin
		for i in 0 to (input'length - 1) loop
			output(input'length-1 - i) := input(i);
		end loop;
		return output;
	end function;

	-- Function to convert from an std_logic input to an integer
	function std_to_integer( s : std_logic ) return integer is
	begin
		if s = '1' then
			return 1;
		else
			return 0;
		end if;
	end function;

begin
	-- unit under test (uut): future-time temporal logic monitor
	uut : ft_monitor
    port map(
		clk                     => s_clk,
		reset_n                 => s_reset_n,
		atomics                 => s_atomics,
		timestamp               => s_rtc_timestamp,
		en                      => s_en,
		trigger					=> s_trigger,
		program_addr            => s_programming_memory_addr,
		program_data            => s_programming_memory_data,
		program_imem            => s_programming_imem,
		program_interval_memory => s_programming_interval_mem,
		violated                => s_violated,
		violated_valid          => s_violated_valid,
		pt_data_memory_addr     => open,
		pt_data_memory_data     => '0',
		sync_out                => open,
		finish                  => open,
		data_memory_async_data  => open,
		data_memory_async_empty => open,
		data_memory_sync_data   => open,
		data_memory_addr        => (others => '0'),

		--Pei: signal for simulation to replace spy function 
		this_new_result         => new_result_spy,
		this_sync_out_data_time => result_time_spy,
		--this_sync_out_data_value => result_value_spy

		--Pei: signal for writing output
		debug => s_debug
		--have_new_result => s_have_new_result,
		--new_result_rdy => s_new_result_rdy,
		--new_result => s_new_result,
		--command => s_command,

		--pc_debug => pc_debug,
		--have_new_result_intermediate => s_have_new_result_intermediate,
		--new_result_rdy_intermediate => s_new_result_rdy_intermediate
	);

	-- Clock signal
	process
	begin
		s_clk <= '0';
		wait for 1 sec / (2 * CLK_FREQ);
		s_clk <= '1';
		if stop = true then
			wait;
		end if;
		wait for 1 sec / (2 * CLK_FREQ);
	end process;

	-- 
	trigger_signal : process
	begin
		wait until s_sutclk = '1';
		s_trigger <= '1';
		wait_cycle(s_clk, 6);
		s_trigger <= '0';
		wait until s_sutclk = '0';
	end process;

	-- 
	p_generate_sut_clk : process
	begin
		s_sutclk <= '0';
		wait for 1 sec / (2 * SUT_FREQ);
		s_sutclk <= '1';
		if stop = true then
			wait;
		end if;
		wait for 1 sec / (2 * SUT_FREQ);
	end process p_generate_sut_clk;

	-- 
	p_rtc : process (s_sutclk, s_rtc_en)
	begin
		if s_sutclk'event and s_sutclk = '1' then
			if s_rtc_en = '1' then
				s_rtc_timestamp <= increment_slv(s_rtc_timestamp);
				if(s_rtc_timestamp = std_logic_vector(to_unsigned(2147483647, s_rtc_timestamp'length))) then
					log_err("s_rtc_timestamp overflow!");
				end if;
			end if;
		end if;
	end process p_rtc;
--------------------------------------------------------------------------------
-- Process for writing the R2U2 instruction and memory binary files to the mu
-- monitor.
--------------------------------------------------------------------------------
	p_write_mumonitor_prom : process
		variable v_file_line_rd    : line;
		variable v_str_line        : string (COMMAND_WIDTH downto 1);
		variable v_str_line_ts     : string (2*TIMESTAMP_WIDTH downto 1);
		variable v_mumon_prom_addr : std_logic_vector(s_programming_memory_addr'length-1 downto 0) := (others => '0');
	begin
		-- Disable the mu monitor's instruction and interval memory write signals
		s_programming_imem         <= '0';
		s_programming_interval_mem <= '0';
		-- Reset the mu monitor; note that the reset signal is "active-low"
		s_reset_n                  <= '0';
		wait_cycle(s_clk, 5);
		-- Turn off the mu monitor's reset signal.
		s_reset_n                  <= '1';
		wait_cycle(s_clk, 20);
		
		
		-- Load the mu monitor's instruction memory from the machine binary file (ftm.bin)
		while not endfile(mumonProgram_file) loop
			-- Read the next line in the file
			readline(mumonProgram_file, v_file_line_rd);
			-- Convert from a line to a string
			read(v_file_line_rd, v_str_line);
			-- Enable the write signal for the mu monitor's instruction memory
			s_programming_imem <= '1';
			-- Set the memory address
			s_programming_memory_addr <= v_mumon_prom_addr;
			-- Data line to mu monitor's instruciton memory
			-- Frontload values with zeros, if the overall length of v_str_line is less than COMMAND_WIDTH
			s_programming_memory_data <= std_logic_vector(to_unsigned(0,s_programming_memory_data'length-v_str_line'length)) & str_to_std_logic_vector(v_str_line);
			-- Wait a clock cycle for the value to be written to the mu monitor's memory.
			wait_cycle(s_clk, 1);
			-- Increment the memory's address (assume it starts at addr 0)
			-- Note that the 'increment_slv' function is in 'testbench_util_pkg.vhd'
			v_mumon_prom_addr := increment_slv(v_mumon_prom_addr);
		end loop;
		
		-- Disable the instruction memory's write bit
		s_programming_imem <= '0';
		
		-- Reset the memory address counter to 0 for the interval memory
		v_mumon_prom_addr  := (others => '0');
		
		-- Load the mu monitor's interval memory from the interval binary file (fti.bin)
		while not endfile(mumonInterval_file) loop
			-- Read the next line from the file.
			readline(mumonInterval_file, v_file_line_rd);
			-- Convert from a line to a string
			read(v_file_line_rd, v_str_line_ts);
			-- Enable the write signal for the mu monitor's interval memroy
			s_programming_interval_mem <= '1';
			-- Set the memory address
			s_programming_memory_addr <= v_mumon_prom_addr;
			-- Data line to mu monitor's interval memory
			-- Frontload values with zeros, if the overall length of v_str_line is less than COMMAND_WIDTH
			s_programming_memory_data <= std_logic_vector(to_unsigned(0,s_programming_memory_data'length-v_str_line_ts'length)) & str_to_std_logic_vector(v_str_line_ts);
			-- Wait a clock cycle for the value to be written to the mu monitor's memory.
			wait_cycle(s_clk, 1);
			-- Increment the memory's address (assume it starts at addr 0)
			-- Note that the 'increment_slv' function is in 'testbench_util_pkg.vhd'
			v_mumon_prom_addr := increment_slv(v_mumon_prom_addr);
		end loop;
		
		-- Disable the interval memory's write bit
		s_programming_interval_mem <= '0';
		
		-- Wait a clock cycle
		wait_cycle(s_clk, 10);
		
		-- Set the 's_programming_stop' variable to true, so that the input process of the testbench knows to start
		s_programming_stop <= true;
		wait;

	end process;
--------------------------------------------------------------------------------
-- Process for printing mu monitor's debug output results
--------------------------------------------------------------------------------
	verify_data_process : process
		variable my_line:  line; 
		variable file_is_open:  boolean;
		variable lastTimeStamp : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0)    := (others => '1');
		variable lastPC : std_logic_vector(log2c(ROM_LEN) - 1 downto 0) :=(others=>'1');
		variable i : integer := 0;
	begin

		wait until rising_edge(s_clk);
		
		
		if s_debug.new_result_rdy_intermediate='1' then
			i := i + 1;
--			report "Print 1:" & to_string(i);
			
			-- Write the current output to the results file.
			if(lastTimeStamp/=s_rtc_timestamp)then
				if(i > 1) then
					write(my_line,string'(" "));
					writeline(testSampleResult_file, my_line);
				end if;
				lastTimeStamp := s_rtc_timestamp;
				write(my_line,string'("----------TIME STEP: "));
				write(my_line,to_integer(unsigned(lastTimeStamp)));
				write(my_line,string'("----------"));
				writeline(testSampleResult_file, my_line);
			end if;
			
			if(s_debug.pc_debug/=lastPC or s_debug.have_new_result_intermediate='1')then
				lastPC := s_debug.pc_debug;
--				report "Print 2:" & to_string(i);
				if s_debug.have_new_result_intermediate='1' then
					-- Preformat the output
					write(my_line,"PC:" & integer'image(to_integer(unsigned(s_debug.pc_debug))));        
					-- Determine the instruction type
					case s_debug.command is
						when OP_LOAD=>
							write(my_line,string'(" LOAD"));
						when OP_FT_NOT=>
							write(my_line,string'(" NOT"));
						when OP_FT_BOXBOX=>
							write(my_line," G[" & integer'image(to_integer(unsigned(s_debug.interval.max))) & "]");
						when OP_FT_BOXDOT=>
							write(my_line," G[" & integer'image(to_integer(unsigned(s_debug.interval.min))) &","&integer'image(to_integer(unsigned(s_debug.interval.max))) & "]");
						when OP_FT_AND=>
							write(my_line,string'(" AND"));
						when OP_FT_UNTIL=>
							write(my_line," U[" & integer'image(to_integer(unsigned(s_debug.interval.min))) &","&integer'image(to_integer(unsigned(s_debug.interval.max))) & "]");
						when OP_END => 
							write(my_line,string'(" END"));
						when OP_END_SEQUENCE=>
							write(my_line,string'(" END_SEQUENCE"));
						when others=>
							write(my_line,string'(" ???"));
					end case;
					-- Determine the value of the output
					if(s_debug.new_result.value='1')then
						write(my_line," = [" & integer'image(to_integer(unsigned(s_debug.new_result.time))) & "," & "True" &"]");
					else
						write(my_line," = [" & integer'image(to_integer(unsigned(s_debug.new_result.time))) & "," & "False" &"]");
					end if;
					-- Write the output to the results file
					writeline(testSampleResult_file, my_line);
				end if;
			end if;
		end if;
	end process;

--------------------------------------------------------------------------------
-- New process for printing r2u2 output
--------------------------------------------------------------------------------
--verify_data_process : process
--		variable my_line       : line; 
--		variable file_is_open  : boolean;
--		variable lastTimeStamp : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0)    := (others => '1');
--		variable lastPC        : std_logic_vector(log2c(ROM_LEN) - 1 downto 0) :=(others=>'1');
--	begin
		-- On every rising clock edge, check the following:
--		wait until rising_edge(s_clk);
		-- 
--		if s_debug.new_result_rdy_intermediate='1' then
			-- Debug print statement to make sure this condition happens
--			report "Print 1";
			-- Write the current timestamp to my_line
--			if(lastTimeStamp/=s_rtc_timestamp)then
--				report "Print 2";
--				lastTimeStamp := s_rtc_timestamp;
--				write(my_line,to_integer(unsigned(lastTimeStamp)));
--				write(my_line,string'(":"));
--			end if;
			-- 
--			if(s_debug.pc_debug=lastPC or s_debug.have_new_result_intermediate='1')then
--				lastPC := s_debug.pc_debug;
--				report "Print 3";
--				if (s_debug.have_new_result_intermediate='1') then --and (s_debug.command=OP_END_SEQUENCE) then
--					if(s_debug.new_result.value='1')then
--						write(my_line,integer'image(to_integer(unsigned(s_debug.new_result.time))) & "," & "T");
--					else
--						write(my_line,integer'image(to_integer(unsigned(s_debug.new_result.time))) & "," & "F");
--					end if;
--					report "Print 4";				
--					writeline(testSampleResult_file, my_line);
--				end if;
--			end if;
--		end if;
--	end process;

--------------------------------------------------------------------------------
-- Process for reading in the comma-separated *.trc files in order to test the 
-- mu monitor.
--------------------------------------------------------------------------------
	p_apply_test_input : process
		-- Note: ATOMICS_WIDTH is defined in log_input_pkg.vhd
		variable v_file_line_rd        : line;
		variable v_str_line            : string(1 downto 1);
		variable v_str_atomics         : string(ATOMICS_WIDTH downto 1);
		variable j                     : integer := 0;
		variable v_atomics             : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
		-- Note: TIMESTAMP_WIDTH is defined in mu_monitor_pkg
		variable v_str_timestamp_delta : string(TIMESTAMP_WIDTH downto 1);
		variable v_timestamp_delta     : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
		variable v_last_output_time    : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0) := (others => '0');
	begin
		wait until s_programming_stop = true;
		wait until (s_sutclk'event and s_sutclk = '1');

		-- set initial atomics values
		s_atomics <= (others => '0');
		wait_cycle(s_sutclk, 1);
		s_en     <= '1';
		wait_cycle(s_sutclk, 1);
		-- activate mu_monitor
		s_rtc_en <= '1';

		-- While-loop for reading in the atomics from the *.trc file
		while not endfile(testSample_file) loop
			-- Read in the test file, line-by-line
			readline(testSample_file, v_file_line_rd);
			j := 0;
			-- For each element in the line, populate just the atomics (i.e., remove the commas from the comma separated input trace file)
			for i in 1 to v_file_line_rd'length loop 
				-- Read a single element in the file
				read(v_file_line_rd, v_str_line);
				-- If the value is not a comma,
				if(v_str_line/=",")then
					-- Increment the position in the v_str_atomics vector
					j := j + 1;
					-- Write the 1 or 0 from v_str_line to the v_str_atomics vector
					v_str_atomics(j downto j) := v_str_line(1 downto 1);
					-- Debug print statement
					--report "Atomic value " & to_string(j) & " is: " & v_str_line;
				end if;
			end loop;
			-- Convert the atomics from a string to std_logic_vector 
			v_atomics := str_to_std_logic_vector(v_str_atomics);
			-- Write the newly input atomics to the mu monitor's s_atomics signal
			s_atomics <= reverse(v_atomics);
			--report "The value of 's_atomics' is " & to_string(s_atomics);
			-- Make the while-loop wait for a single clock-cycle
			wait_cycle(s_sutclk, 1);
			-- Debug statement that prints the value of s_atomics to the terminal. 
			-- Note that it must be after the wait, because of how the "<=" operator works for VHDL
			--report "The value of 's_atomics' is " & to_string(s_atomics);
		end loop;
		
		s_en <= '0';
		stop <= true;
		wait;
		
	end process;
end architecture;
