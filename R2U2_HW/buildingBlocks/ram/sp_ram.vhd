-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : dp_ram.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: dual port ram
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

use work.math_pkg.all;
use ieee.numeric_std.all;

entity sp_ram is
  generic (
    ADDR_WIDTH : integer;                                    -- address width
    DATA_WIDTH : integer                                  -- data width
    );
  port (
    clk     : in  std_logic;                                  -- clock signal
    addr    : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
    wrData  : in  std_logic_vector(DATA_WIDTH-1 downto 0);  -- write data
    write   : in  std_logic;
    rdData  : out std_logic_vector(DATA_WIDTH-1 downto 0)   -- read data
    );
end entity;


architecture beh of sp_ram is
  subtype ram_entry is std_logic_vector(DATA_WIDTH - 1 downto 0);
  type    ram_type is array(0 to (2 ** ADDR_WIDTH) - 1) of ram_entry;
  --signal  ram : ram_type := (others => (others => '1'));
    signal  ram : ram_type := (others => (others => '0'));
begin

  sync : process(clk)
  begin
    if rising_edge(clk) then
      if write = '1' then
        ram(to_integer(unsigned(addr))) <= wrData;
      end if;

      rdData <= ram(to_integer(unsigned(addr)));
    end if;
  end process sync;

end architecture;
