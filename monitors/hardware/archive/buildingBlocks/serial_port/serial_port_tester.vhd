library ieee;
use ieee.std_logic_1164.all;

entity serial_port_tester is
  port
  (
    sys_clk, sys_res_n : in std_logic;
    segs_a            : out   std_logic_vector(6 downto 0);
    segs_b            : out   std_logic_vector(6 downto 0);
    rx : in std_logic;
    tx : out std_logic
  );
end entity serial_port_tester;
