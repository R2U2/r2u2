-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : sync.vhd
-- Author     : Thomas Polzer
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A general purpose synchronizer implementation 
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

-- serial connection of flip-flops to avoid latching of metastable inputs at
-- the analog/digital interface
entity sync is
  generic
    (
      -- number of stages in the input synchronizer
      SYNC_STAGES : integer range 2 to integer'high;
      -- reset value of the output signal
      RESET_VALUE : std_logic
      );
  port
    (
      clk   : in std_logic;
      res_n : in std_logic;

      data_in  : in  std_logic;
      data_out : out std_logic
      );
end entity sync;
