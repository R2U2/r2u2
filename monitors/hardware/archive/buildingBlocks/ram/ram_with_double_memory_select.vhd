-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : ram_with_double_memory_select.vhd
-- Author     : Patrick Moosbrugger
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A general purpose RAM implementation
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pkg.all;

entity ram_with_double_memory_select is
  generic
    (
      -- address width
      ADDR_WIDTH          : integer;
      -- data width
      DATA_WIDTH          : integer;
      -- width of the memory_select input
      MEMBUS_WR_SELECT_WIDTH : integer;

      MEMBUS_RD_SELECT_WIDTH : integer;
      -- the id of the current write port
      MEMBUS_WR_SELECT_ID    : std_logic_vector;
      -- the id of the current read port
      MEMBUS_RD_SELECT_ID    : std_logic_vector
      );
  port
    (
      clk : in std_logic;

      raddr            : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
      rdata            : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      rd               : in  std_logic;
      rd_memory_select : in  std_logic_vector(MEMBUS_RD_SELECT_WIDTH - 1 downto 0);

      waddr            : in std_logic_vector(ADDR_WIDTH - 1 downto 0);
      wdata            : in std_logic_vector(DATA_WIDTH - 1 downto 0);
      wr               : in std_logic;
      wr_memory_select : in std_logic_vector(MEMBUS_WR_SELECT_WIDTH - 1 downto 0)
      );
end entity ram_with_double_memory_select;

architecture ram_beh of ram_with_double_memory_select is
  subtype ram_entry is std_logic_vector(DATA_WIDTH - 1 downto 0);
  type    ram_type is array(0 to (2 ** ADDR_WIDTH) - 1) of ram_entry;
  signal  ram : ram_type := (others => (others => '0'));
begin

  sync : process(clk)
  begin
    if rising_edge(clk) then
      if wr = '1' and wr_memory_select = MEMBUS_WR_SELECT_ID then
        ram(to_integer(unsigned(waddr))) <= wdata;
      end if;
      if rd = '1' and rd_memory_select = MEMBUS_RD_SELECT_ID then
        rdata <= ram(to_integer(unsigned(raddr)));
      else
        rdata <= (others => 'Z');
      end if;
    end if;

  end process sync;

end architecture ram_beh;
