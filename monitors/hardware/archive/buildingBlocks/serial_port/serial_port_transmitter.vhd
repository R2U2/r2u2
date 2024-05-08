----------------------------------------------------------------------------------
-- Company:      TU Wien - ECS Group                                            --
-- Engineer:     Thomas Polzer                                                  --
--                                                                              --
-- Create Date:  21.09.2010                                                     --
-- Design Name:  DIDELU                                                         --
-- Module Name:  serial_port_transmitter                                        --
-- Project Name: DIDELU                                                         --
-- Description:  Serial Transmitter - Entity                                    --
----------------------------------------------------------------------------------

----------------------------------------------------------------------------------
--                                LIBRARIES                                     --
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

----------------------------------------------------------------------------------
--                                 ENTITY                                       --
----------------------------------------------------------------------------------

-- serial port transmitter
entity serial_port_transmitter is
  generic
  (
    CLK_DIVISOR : integer
  );
  port
  (
    clk, res_n         : in  std_logic;
    data               : in  std_logic_vector(7 downto 0);
    empty              : in  std_logic;
    rd                 : out std_logic;
    
    tx                 : out std_logic
  );
end entity serial_port_transmitter;

--- EOF ---
