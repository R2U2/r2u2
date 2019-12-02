-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : mu_monitor_tb.vhd
-- Author     : Patrick Moosbrugger (p.moosbrugger@gmail.com)
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: testbench for the mu_monitor
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
--use ieee.std_logic_unsigned.all;
use work.ft_mu_monitor_pkg.all;
use work.mu_monitor_pkg.all;
use work.log_input_pkg.all;

use work.testbench_util_pkg.all;
use std.textio.all;
--use work.cevrvu_top_pkg.all;
--library modelsim_lib;
--use modelsim_lib.util.all;
use work.math_pkg.all;

entity tb is
  generic (
    imemFilePath  : string := "../testcases/tmp.ftm";    
    intFilePath   : string := "../testcases/tmp.fti";
    inputFilePath : string := "../testcases/atomic.trc";
    outputFilePath : string := "../result/async_out.txt"
    );
end entity;

architecture sim of tb is
  constant CLK_FREQ                   : integer                                         := 100000000;
  constant SUT_FREQ                   : integer                                         := 100000;
--  constant SUT_FREQ                   : integer                                         := 2000000;
  --constant ATOMICS_WIDTH              : integer                                         := 2;
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
  --signal   s_programming_memory_data  : std_logic_vector (2*TIMESTAMP_WIDTH-1 downto 0) := (others => '0');
  signal   s_programming_memory_data  : std_logic_vector (MEMBUS_DATA_WIDTH-1 downto 0) := (others => '0');
  signal   s_violated                 : std_logic                                       := '0';
  signal   s_violated_valid           : std_logic                                       := '0';
  file mumonProgram_file              : text open read_mode is imemFilePath;
  file mumonInterval_file             : text open read_mode is intFilePath;
  file testSample_file                : text open read_mode is inputFilePath;
  file testSampleResult_file          : text open write_mode is outputFilePath;
  signal   s_rtc_en                   : std_logic                                       := '0';
  
  -- spy signals
  signal new_result_spy	: std_logic;
  signal result_time_spy : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
 

  --write output signal
  signal s_debug : debug_t;


  function reverse(input : std_logic_vector) return std_logic_vector is
    variable output : std_logic_vector(input'length - 1 downto 0);
  begin
    for i in 0 to (input'length - 1) loop
      output(input'length-1 - i) := input(i);
    end loop;
    return output;
  end function;

  function std_to_integer( s : std_logic ) return integer is
  begin
    if s = '1' then
      return 1;
    else
      return 0;
    end if;
  end function;

begin
  dut : ft_mu_monitor
    port map
    (
      clk                     => s_clk,
      reset_n                 => s_reset_n,
      atomics                 => s_atomics,
      timestamp               => s_rtc_timestamp,
      en                      => s_en,
      trigger				=> s_trigger,
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
      
--   spy : process
--  begin
--    init_signal_spy("/tb/dut/ift_mu_monitor_fsm/this.new_result", "/tb/new_result_spy");
--    init_signal_spy("/tb/dut/ift_mu_monitor_fsm/this.sync_out.data.time", "/tb/result_time_spy");
--    init_signal_spy("/tb/dut/ift_mu_monitor_fsm/this.sync_out.data.value", "/tb/result_value_spy");
--    wait;
--  end process;

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

trigger_signal : process
begin
  wait until s_sutclk = '1';
  s_trigger <= '1';
  wait_cycle(s_clk, 6);
  s_trigger <= '0';
  wait until s_sutclk = '0';
end process;

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

  p_write_mumonitor_prom : process
    variable v_file_line_rd    : line;
    variable v_str_line        : string (COMMAND_WIDTH downto 1);
    --variable v_str_line_ts     : string (32 downto 1);
    variable v_str_line_ts     : string (2*TIMESTAMP_WIDTH downto 1);
    variable v_mumon_prom_addr : std_logic_vector(s_programming_memory_addr'length-1 downto 0) := (others => '0');
  begin
    --s_programming_memory_data  <= (others=>'0');
    --s_programming_memory_addr  <= (others=>'0');
    s_programming_imem         <= '0';
    s_programming_interval_mem <= '0';
    s_reset_n                  <= '0';
    wait_cycle(s_clk, 5);
    s_reset_n                  <= '1';
    wait_cycle(s_clk, 20);


    while not endfile(mumonProgram_file) loop
      readline(mumonProgram_file, v_file_line_rd);
      read(v_file_line_rd, v_str_line);
      
      s_programming_imem        <= '1';
      s_programming_memory_addr <= v_mumon_prom_addr;
      --s_programming_memory_data only use (COMMAND_WIDTH-1 downto 0)
      s_programming_memory_data <= std_logic_vector(to_unsigned(0,s_programming_memory_data'length-v_str_line'length)) & str_to_std_logic_vector(v_str_line);
      wait_cycle(s_clk, 1);
      -- increment prom address;
      v_mumon_prom_addr         := increment_slv(v_mumon_prom_addr);
    end loop;

    s_programming_imem <= '0';
    v_mumon_prom_addr  := (others => '0');


    while not endfile(mumonInterval_file) loop
      readline(mumonInterval_file, v_file_line_rd);
      read(v_file_line_rd, v_str_line_ts);

      s_programming_interval_mem <= '1';
      s_programming_memory_addr  <= v_mumon_prom_addr;
      --s_programming_memory_data only use (2*TIMESTAMP_WIDTH-1 downto 0)
      s_programming_memory_data  <= std_logic_vector(to_unsigned(0,s_programming_memory_data'length-v_str_line_ts'length)) & str_to_std_logic_vector(v_str_line_ts);
      wait_cycle(s_clk, 1);
      -- increment prom address;
      v_mumon_prom_addr          := increment_slv(v_mumon_prom_addr);
    end loop;

    s_programming_interval_mem <= '0';

    wait_cycle(s_clk, 10);

    s_programming_stop <= true;
    wait;
    -- finished programming

  end process;


verify_data_process : process
      variable my_line:  line; 
      --file l_file:       TEXT;  
      variable file_is_open:  boolean;
      --variable whichCommand: string(1 to 4);
      variable lastTimeStamp : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0)    := (others => '1');
      variable lastPC : std_logic_vector(log2c(ROM_LEN) - 1 downto 0) :=(others=>'1');
  begin -- process
--    if not file_is_open then
--      file_open (l_file,testSampleResult_file, write_mode);
--      file_is_open := true;
--      write(my_line, string'("**********RESULTS**********"));
--      writeline(l_file, my_line);
--    end if;
    wait until rising_edge(s_clk);

    if s_debug.new_result_rdy_intermediate='1' then

      if(lastTimeStamp/=s_rtc_timestamp)then
        lastTimeStamp := s_rtc_timestamp;
        --writeline(l_file, my_line);
        write(my_line,string'(""));
        writeline(testSampleResult_file, my_line);

        write(my_line,string'("----------TIME STEP: "));
        write(my_line,to_integer(unsigned(lastTimeStamp)));
        write(my_line,string'("----------"));
        writeline(testSampleResult_file, my_line);
      end if;

      -- The following code is workable. I just want to change the output to match with the regression test output format
      --if(s_debug.pc_debug/=lastPC or s_debug.have_new_result_intermediate='1')then
      --  lastPC := s_debug.pc_debug;
      --  case s_debug.command is
      --    when OP_LOAD=>
      --      write(my_line,string'("LOAD "));
      --    when OP_FT_NOT=>
      --      write(my_line,string'("NOT "));
      --    when OP_FT_BOXBOX=>
      --      write(my_line,"G[" & integer'image(to_integer(unsigned(s_debug.interval.max))) & "] ");
      --    when OP_FT_BOXDOT=>
      --      write(my_line,"G[" & integer'image(to_integer(unsigned(s_debug.interval.min))) &","&integer'image(to_integer(unsigned(s_debug.interval.max))) & "] ");
      --    when OP_FT_AND=>
      --      write(my_line,string'("AND "));
      --    when OP_FT_UNTIL=>
      --      write(my_line,"U[" & integer'image(to_integer(unsigned(s_debug.interval.min))) &","&integer'image(to_integer(unsigned(s_debug.interval.max))) & "] ");

      --    when OP_END_SEQUENCE=>
      --      write(my_line,string'("END "));
      --    when others=>
      --      write(my_line,string'("??? "));
      --  end case;
      --  if s_debug.have_new_result_intermediate='1' then
      --    write(my_line,"PC:" & integer'image(to_integer(unsigned(s_debug.pc_debug))) & " = (" & integer'image(std_to_integer(s_debug.new_result.value)) & "," & integer'image(to_integer(unsigned(s_debug.new_result.time))) &")");
      --  else 
      --    write(my_line,"PC:" & integer'image(to_integer(unsigned(s_debug.pc_debug))) & " = (-,-)");
      --  end if;
      --  writeline(testSampleResult_file, my_line);
      --end if;
      if(s_debug.pc_debug/=lastPC or s_debug.have_new_result_intermediate='1')then
        lastPC := s_debug.pc_debug;
       
        if s_debug.have_new_result_intermediate='1' then
          write(my_line,"PC:" & integer'image(to_integer(unsigned(s_debug.pc_debug))));        
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

            when OP_END_SEQUENCE=>
              write(my_line,string'(" END"));
            when others=>
              write(my_line,string'(" ???"));
          end case;

          if(s_debug.new_result.value='1')then
            write(my_line," = [" & integer'image(to_integer(unsigned(s_debug.new_result.time))) & "," & "True" &"]");
          else
            write(my_line," = [" & integer'image(to_integer(unsigned(s_debug.new_result.time))) & "," & "False" &"]");
          end if;        
          writeline(testSampleResult_file, my_line);

        end if;
      end if;
    end if;
  end process;





  p_apply_test_input : process
    variable v_file_line_rd        : line;
    variable v_str_line            : string(ATOMICS_WIDTH downto 1);
    variable v_str_atomics         : string(ATOMICS_WIDTH downto 1);
    variable v_str_timestamp_delta : string(TIMESTAMP_WIDTH downto 1);
    variable v_atomics             : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
    variable v_timestamp_delta     : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
    variable v_last_output_time    : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0) := (others => '0');
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

    --log_to_file_ts("Start applying test input, enabling RTC", s_rtc_timestamp, log_file);
    while not endfile(testSample_file) loop
      readline(testSample_file, v_file_line_rd);
      read(v_file_line_rd, v_str_line);

      -- disassemble the read line
      v_str_atomics := v_str_line(ATOMICS_WIDTH downto 1);
      v_atomics     := str_to_std_logic_vector(v_str_atomics);
--      report "The value of 'v_atomics' is " & to_string(v_atomics);
      -- apply new atomic propositions
      s_atomics <= reverse(v_atomics);
      -- wait for given delta
      wait_cycle(s_sutclk, 1);


    end loop;


    s_en <= '0';
    stop <= true;

    wait;
  end process;
end architecture;
