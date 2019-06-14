library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package log_input_pkg is


    constant ATOMICS_WIDTH : integer := 128;
  
    constant ATC_ADDR_WIDTH : integer := 11;
    constant ATC_DATA_WIDTH : integer := 32;
    constant LOG_DATA_WIDTH : integer := 570;
end log_input_pkg;
