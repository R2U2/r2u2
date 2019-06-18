----------------------------------------------------------------------------------
-- Company: 
-- Engineer: 
-- 
-- Create Date: 11/27/2017 01:52:54 PM
-- Design Name: 
-- Module Name: uart_pkg - 
-- Project Name: 
-- Target Devices: 
-- Tool Versions: 
-- Description: 
-- 
-- Dependencies: 
-- 
-- Revision:
-- Revision 0.01 - File Created
-- Additional Comments:
-- 
----------------------------------------------------------------------------------


library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

package uart_pkg is
    
    function str_to_std_logic_vector(input :    string) return std_logic_vector;
    constant data_size: integer:=1024;--for simulation purpose
    type TEST_DATA_type is array (0 to data_size-1) of std_logic_vector(7 downto 0);
    
    
end uart_pkg;

package body uart_pkg is

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

end uart_pkg;
