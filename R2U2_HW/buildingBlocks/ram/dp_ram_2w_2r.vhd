
library ieee;
use ieee.std_logic_1164.all;
use IEEE.NUMERIC_STD.ALL;
use work.ram_pkg.all;

entity dp_ram_2w_2r is
  generic (
    ADDR_WIDTH : integer;   -- address width
    DATA_WIDTH : integer    -- data width
    );
  port (
    clk     : in  std_logic;                                  -- clock signal
    rdAddrA : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
    rdAddrB : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- read address
    wrAddr  : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);  -- write address
    wrData  : in  std_logic_vector(DATA_WIDTH - 1 downto 0);  -- write data
    write   : in  std_logic;
    rdDataA    : out std_logic_vector(DATA_WIDTH - 1 downto 0);-- read data
    rdDataB    : out std_logic_vector(DATA_WIDTH - 1 downto 0)-- read data 
  
--    clk         : in  std_logic;                                
--    addr_1      : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
--    addr_2      : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
--    wrData_1    : in  std_logic_vector(DATA_WIDTH  - 1 downto 0);
--    wrData_2    : in  std_logic_vector(DATA_WIDTH  - 1 downto 0);
--    write_1     : in  std_logic;
--    write_2     : in  std_logic;
--    rdData_1    : out std_logic_vector(DATA_WIDTH - 1 downto 0);
--    rdData_2    : out std_logic_vector(DATA_WIDTH - 1 downto 0)
    );
end entity;

architecture beh of dp_ram_2w_2r is
--  subtype ram_entry is std_logic_vector(DATA_WIDTH - 1 downto 0);
--  type    ram_type is array(0 to (2 ** ADDR_WIDTH) - 1) of ram_entry;
--  signal  ram : ram_type := (others => (others => '0'));
begin

--  sync : process(clk)
--  begin
--    if rising_edge(clk) then
--      if write_1 = '1' then
--        ram(to_integer(unsigned(addr_1))) <= wrData_1;
--      end if;
--      if write_2 = '1' then
--        ram(to_integer(unsigned(addr_2))) <= wrData_2;
--      end if;
--      rdData_1 <= ram(to_integer(unsigned(addr_1)));
--      rdData_2 <= ram(to_integer(unsigned(addr_2)));
--    end if;
--  end process sync;

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


end architecture;

--begin

--  ram1 : dp_ram_wt
--    generic map(
--      ADDR_WIDTH => ADDR_WIDTH,
--      DATA_WIDTH => DATA_WIDTH
--      )
--    port map(
--      clk    => clk,
--      rdAddr => rdAddrA,
--      wrAddr => wrAddr,
--      wrData => wrData,
--      write  => write,
--      rdData => rdDataA
--      );

--  ram2 : dp_ram_wt
--    generic map(
--      ADDR_WIDTH => ADDR_WIDTH,
--      DATA_WIDTH => DATA_WIDTH
--      )
--    port map(
--      clk    => clk,
--      rdAddr => rdAddrB,
--      wrAddr => wrAddr,
--      wrData => wrData,
--      write  => write,
--      rdData => rdDataB
--      );

--  ramC : dp_ram_wt
--    generic map(
--      ADDR_WIDTH => ADDR_WIDTH,
--      DATA_WIDTH => DATA_WIDTH
--      )
--    port map(
--      clk    => clk,
--      rdAddr => rdAddrC,
--      wrAddr => wrAddr,
--      wrData => wrData,
--      write  => write,
--      rdData => rdDataC
--      );

--end architecture;

