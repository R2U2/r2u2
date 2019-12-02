-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : ram.vhd
-- Author     : Daniel Schachinger
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A general purpose RAM implementation
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pkg.all;

entity ram is
  generic
    (
      -- address width
      ADDR_WIDTH : integer;
      -- data width
      DATA_WIDTH : integer
      );
  port
    (
      clk : in std_logic;

      raddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
      rdata : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      rd    : in  std_logic;

      waddr : in std_logic_vector(ADDR_WIDTH - 1 downto 0);
      wdata : in std_logic_vector(DATA_WIDTH - 1 downto 0);
      wr    : in std_logic
      );
end entity ram;

architecture ram_beh of ram is
  subtype ram_entry is std_logic_vector(DATA_WIDTH - 1 downto 0);
  type    ram_type is array(0 to (2 ** ADDR_WIDTH) - 1) of ram_entry;
  signal  ram : ram_type := (others => (others => '0'));
begin

  sync : process(clk)
  begin
    if rising_edge(clk) then
      if wr = '1' then
        ram(to_integer(unsigned(waddr))) <= wdata;
      end if;
      if rd = '1' then
        rdata <= ram(to_integer(unsigned(raddr)));
      end if;
    end if;
  end process sync;

end architecture ram_beh;
