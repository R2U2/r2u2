-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : ram_with_reset_and_ack.vhd
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

entity ram_with_reset_and_ack is
  generic
    (
      -- address width
      ADDR_WIDTH  : integer;
      -- data width
      DATA_WIDTH  : integer;
      RESET_VALUE : std_logic_vector
      );
  port
    (
      clk     : in std_logic;
      reset_n : in std_logic;

      raddr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
      rdata : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      rd    : in  std_logic;
      rack  : out std_logic;

      waddr : in std_logic_vector(ADDR_WIDTH - 1 downto 0);
      wdata : in std_logic_vector(DATA_WIDTH - 1 downto 0);
      wr    : in std_logic
      );
end entity ram_with_reset_and_ack;

architecture ram_beh of ram_with_reset_and_ack is
  subtype ram_entry is std_logic_vector(DATA_WIDTH - 1 downto 0);
  type    ram_type is array(0 to (2 ** ADDR_WIDTH) - 1) of ram_entry;
  signal  ram : ram_type := (others => (others => '0'));
begin

  sync : process(clk, reset_n)
  begin
    if reset_n = '0' then
      rdata <= RESET_VALUE;
      ram <= (others => (others => '0'));
      rack <= '0';
    elsif rising_edge(clk) then
      rack <= '0';
      if wr = '1' then
        ram(to_integer(unsigned(waddr))) <= wdata;
      end if;
      if rd = '1' then
        rdata <= ram(to_integer(unsigned(raddr)));
        rack  <= '1';
      end if;
    end if;
  end process sync;

end architecture ram_beh;
