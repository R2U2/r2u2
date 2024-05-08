------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : testbench_util_pkg.vhd
-- Author     : Thomas Reinbacher
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: Some useful helper functions for testbenches                                  
-- most of the str helper functions are adapted from "stefanvhdl.com"
-------------------------------------------------------------------------------  


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

package testbench_util_pkg is
  
  procedure wait_cycle(signal clk        : in std_logic; constant cycle_cnt : in integer);
  function std_logic_vector_to_str(input :    std_logic_vector) return string;
  function str_to_std_logic_vector(input :    string) return std_logic_vector;
  function to_upper(c                    :    character) return character;
  function to_lower(c                    :    character) return character;
  function to_upper(str                  :    string) return string;
  function to_lower(str                  :    string) return string;
  -- print string to a file and start new line
  procedure println(file out_file        :    text; str : in string);
  -- print character to a file and start new line
  procedure println(file out_file        :    text; chr : in character);
  procedure str_read(file in_file        :    text; str : out string);
  function increment_slv(input : std_logic_vector) return std_logic_vector;
  function decrement_slv(input : std_logic_vector) return std_logic_vector;
  procedure log_info(str : in string);
  procedure log_err(str : in string);
  procedure log_to_file_ts(str: in string; rtc : in std_logic_vector; file out_file : text);
end testbench_util_pkg;

package body testbench_util_pkg is
  procedure wait_cycle(signal clk : in std_logic; constant cycle_cnt : in integer) is
  begin
    for i in 1 to cycle_cnt loop
      wait until rising_edge(clk);
    end loop;
  end wait_cycle;

  procedure println(file out_file : text; str : in string) is
    variable l : line;
  begin
    write(l, str);
    writeline(out_file, l);
  end println;

  procedure log_info(str : in string) is
  begin
   assert (false) report "" & str severity note;
  end log_info;

  procedure log_err(str : in string) is
  begin
   assert (false) report "" & str severity error;
  end log_err;
 
  procedure log_to_file_ts(str: in string; rtc : in std_logic_vector; file out_file : text) is
  begin
   println(out_file, integer'image(to_integer(unsigned(rtc))) & ": " & str);
  end log_to_file_ts;    
  
  procedure println(file out_file : text; chr : in character) is
    variable l : line;
  begin
    write(l, chr);
    writeline(out_file, l);
  end println;

  procedure str_read(file in_file : text; str : out string) is
    variable read_line : line;
    variable c         : character;
    variable is_string : boolean;
  begin
    readline(in_file, read_line);
    -- clear the contents of the result string
    for i in str'range loop
      str(i) := ' ';
    end loop;
    -- read all characters of the line, up to the length  
    -- of the results string
    for i in str'range loop
      read(read_line, c, is_string);
      str(i) := c;
      if not is_string then             -- found end of line
        exit;
      end if;
    end loop;
  end str_read;
  
  function std_logic_vector_to_str(input : std_logic_vector) return string is
    variable tmp : string(input'length downto 1) := (others => 'X');
  begin
    for i in input'reverse_range loop
      if (input(i) = '1') then
        tmp(i+1) := '1';
      elsif(input(i) = '0') then
        tmp(i+1) := '0';
      end if;
    end loop;
    return tmp;
  end function std_logic_vector_to_str;

  function str_to_std_logic_vector(input : string) return std_logic_vector is
    variable tmp : std_logic_vector(input'length-1 downto 0) := (others => 'X');
  begin
    for i in 1 to input'length loop
      if(input(i) = '1') then
        tmp(i-1) := '1';
      elsif (input(i) = '0') then
        tmp(i-1) := '0';
      else                              -- Bad Characters
        tmp(i-1) := 'X';
      end if;
    end loop;
    return tmp;
  end function str_to_std_logic_vector;

  function to_upper(str : string) return string is
    variable uppercase_str : string (str'range);
  begin
    for i in str'range loop
      uppercase_str(i) := to_upper(str(i));
    end loop;
    return uppercase_str;
  end to_upper;

  function to_lower(str : string) return string is
    variable lowercase_str : string (str'range);
  begin
    for i in str'range loop
      lowercase_str(i) := to_lower(str(i));
    end loop;
    return lowercase_str;
  end to_lower;

  function to_upper(c : character) return character is
    variable upper : character;
  begin
    case c is
      when 'a'    => upper := 'A';
      when 'b'    => upper := 'B';
      when 'c'    => upper := 'C';
      when 'd'    => upper := 'D';
      when 'e'    => upper := 'E';
      when 'f'    => upper := 'F';
      when 'g'    => upper := 'G';
      when 'h'    => upper := 'H';
      when 'i'    => upper := 'I';
      when 'j'    => upper := 'J';
      when 'k'    => upper := 'K';
      when 'l'    => upper := 'L';
      when 'm'    => upper := 'M';
      when 'n'    => upper := 'N';
      when 'o'    => upper := 'O';
      when 'p'    => upper := 'P';
      when 'q'    => upper := 'Q';
      when 'r'    => upper := 'R';
      when 's'    => upper := 'S';
      when 't'    => upper := 'T';
      when 'u'    => upper := 'U';
      when 'v'    => upper := 'V';
      when 'w'    => upper := 'W';
      when 'x'    => upper := 'X';
      when 'y'    => upper := 'Y';
      when 'z'    => upper := 'Z';
      when others => upper := c;
    end case;
    return upper;
  end to_upper;

  -- convert a character to lower case

  function to_lower(c : character) return character is
    variable lower : character;
  begin
    case c is
      when 'A'    => lower := 'a';
      when 'B'    => lower := 'b';
      when 'C'    => lower := 'c';
      when 'D'    => lower := 'd';
      when 'E'    => lower := 'e';
      when 'F'    => lower := 'f';
      when 'G'    => lower := 'g';
      when 'H'    => lower := 'h';
      when 'I'    => lower := 'i';
      when 'J'    => lower := 'j';
      when 'K'    => lower := 'k';
      when 'L'    => lower := 'l';
      when 'M'    => lower := 'm';
      when 'N'    => lower := 'n';
      when 'O'    => lower := 'o';
      when 'P'    => lower := 'p';
      when 'Q'    => lower := 'q';
      when 'R'    => lower := 'r';
      when 'S'    => lower := 's';
      when 'T'    => lower := 't';
      when 'U'    => lower := 'u';
      when 'V'    => lower := 'v';
      when 'W'    => lower := 'w';
      when 'X'    => lower := 'x';
      when 'Y'    => lower := 'y';
      when 'Z'    => lower := 'z';
      when others => lower := c;
    end case;
    return lower;
  end to_lower;

  function increment_slv(input : std_logic_vector) return std_logic_vector is
     variable tmp : std_logic_vector(input'length-1 downto 0) := (others => '0');
     begin
        tmp := std_logic_vector(unsigned(input) + 1);
        return tmp;
  end function increment_slv;

  function decrement_slv(input : std_logic_vector) return std_logic_vector is
     variable tmp : std_logic_vector(input'length-1 downto 0) := (others => '0');
     begin
        tmp := std_logic_vector(unsigned(input) - 1);
        return tmp;
  end function decrement_slv;         

end package body testbench_util_pkg;
