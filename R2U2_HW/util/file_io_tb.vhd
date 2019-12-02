------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : file_io_tb.vhd
-- Author     : Thomas Reinbacher
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A demonstration on how to use the testbench utils                                  
-------------------------------------------------------------------------------      

library ieee;
use ieee.std_logic_1164.all;
use std.textio.all;
use work.testbench_util_pkg.all;

entity file_io_tb is
end entity file_io_tb;

architecture file_io_tb of file_io_tb is
  constant DATA_LENGTH : integer   := 32;
  signal   d           : std_logic_vector(DATA_LENGTH-1 downto 0);
  signal   fin         : std_logic := '0';
  file log_file        : text open write_mode is "mylog.log";

begin

  p_write_usage : process
  begin
    println(log_file, "hello hello hello");
    wait until fin = '1';
  end process p_write_usage;


  p_read_input : process
    file test_input_file  : text;
    file test_output_file : text;
    variable read_line    : std_logic_vector(DATA_LENGTH-1 downto 0);
    variable write_line   : std_logic_vector(DATA_LENGTH-1 downto 0);
    variable str_line     : string(DATA_LENGTH downto 1);
    variable file_line_rd : line;
    variable file_line_wr : line;

  begin
    -- Open the file:
    file_open(test_input_file, "tst_input.txt", read_mode);
    file_open(test_output_file, "tst_output.txt", write_mode);

    while not endfile(test_input_file) loop
      readline(test_input_file, file_line_rd);
      read(file_line_rd, str_line);
      assert (false) report "Reading " & str_line severity note;
      read_line := str_to_std_logic_vector(str_line);
      d         <= read_line;
      -- Write into out file
      write(file_line_wr, std_logic_vector_to_str(d));
      writeline(test_output_file, file_line_wr);
      wait for 10 ns;
    end loop;

    file_close(test_input_file);

    fin <= '1';
  end process p_read_input;
end architecture file_io_tb;


configuration file_io_tb_cfg of file_io_tb is
  for file_io_tb
  end for;
end file_io_tb_cfg;


