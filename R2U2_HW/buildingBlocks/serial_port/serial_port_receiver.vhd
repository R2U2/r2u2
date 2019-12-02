----------------------------------------------------------------------------------
-- Company:      TU Wien - ECS Group                                            --
-- Engineer:     Thomas Polzer                                                  --
--                                                                              --
-- Create Date:  21.09.2010                                                     --
-- Design Name:  DIDELU                                                         --
-- Module Name:  serial_port_receiver                                           --
-- Project Name: DIDELU                                                         --
-- Description:  Serial Receiver - Entity                                       --
----------------------------------------------------------------------------------

----------------------------------------------------------------------------------
--                                LIBRARIES                                     --
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

----------------------------------------------------------------------------------
--                                 ENTITY                                       --
----------------------------------------------------------------------------------

-- Serial port receiver
entity serial_port_receiver is
  generic
  (
    -- clock frequency [Hz]
    CLK_DIVISOR : integer
  );
  port
  (
    clk, res_n         : in  std_logic;

    data               : out std_logic_vector(7 downto 0);
    data_new           : out std_logic;

    -- receive port
    rx                 : in  std_logic
  );
end entity serial_port_receiver;

--- EOF ---