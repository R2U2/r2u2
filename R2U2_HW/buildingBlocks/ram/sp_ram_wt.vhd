------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : ram.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: single port ram with write through read characteristic
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pkg.all;

entity sp_ram_wt is
  generic (
    ADDR_WIDTH : integer;                                    -- address width
    DATA_WIDTH : integer                                     -- data width
    );
  port (
    clk    : in  std_logic;                                  -- clock signal
    addr   : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read data
    write  : in  std_logic;
    wrData : in  std_logic_vector(DATA_WIDTH - 1 downto 0);  -- read data
    rdData : out std_logic_vector(DATA_WIDTH - 1 downto 0)   -- read data
    );
end entity;


architecture beh of sp_ram_wt is
  subtype ram_entry is std_logic_vector(DATA_WIDTH - 1 downto 0);
  type    ram_type is array(0 to (2 ** ADDR_WIDTH) - 1) of ram_entry;
  signal  ram    : ram_type := (others => (others => '0'));
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
