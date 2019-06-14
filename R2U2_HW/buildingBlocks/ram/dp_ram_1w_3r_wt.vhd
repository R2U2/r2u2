-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : dp_ram_1w_3r_wt.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: ram with 1 write and 3 read ports and write through read characteristic
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use work.ram_pkg.all;

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

entity dp_ram_1w_3r_wt is
  generic (
    ADDR_WIDTH : integer;                                     -- address width
    DATA_WIDTH : integer                                      -- data width
    );
  port (
    clk     : in  std_logic;                                  -- clock signal
    rdAddrA : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
    rdAddrB : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
    rdAddrC : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
    wrAddr  : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- write address
    wrData  : in  std_logic_vector(DATA_WIDTH - 1 downto 0);  -- write data
    write   : in  std_logic;
    rdDataA : out std_logic_vector(DATA_WIDTH - 1 downto 0);  -- read data
    rdDataB : out std_logic_vector(DATA_WIDTH - 1 downto 0);  -- read data
    rdDataC : out std_logic_vector(DATA_WIDTH - 1 downto 0)   -- read data
    );
end entity;

architecture arch of dp_ram_1w_3r_wt is

begin

  ramA : dp_ram_wt
    generic map(
      ADDR_WIDTH => ADDR_WIDTH,
      DATA_WIDTH => DATA_WIDTH
      )
    port map(
      clk    => clk,
      rdAddr => rdAddrA,
      wrAddr => wrAddr,
      wrData => wrData,
      write  => write,
      rdData => rdDataA
      );

  ramB : dp_ram_wt
    generic map(
      ADDR_WIDTH => ADDR_WIDTH,
      DATA_WIDTH => DATA_WIDTH
      )
    port map(
      clk    => clk,
      rdAddr => rdAddrB,
      wrAddr => wrAddr,
      wrData => wrData,
      write  => write,
      rdData => rdDataB
      );

  ramC : dp_ram_wt
    generic map(
      ADDR_WIDTH => ADDR_WIDTH,
      DATA_WIDTH => DATA_WIDTH
      )
    port map(
      clk    => clk,
      rdAddr => rdAddrC,
      wrAddr => wrAddr,
      wrData => wrData,
      write  => write,
      rdData => rdDataC
      );

end architecture;

