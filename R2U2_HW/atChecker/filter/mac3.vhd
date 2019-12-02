-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : mac3.vhd
-- Author     : Johannes Geist <>
-- Copyright  : 2014
-------------------------------------------------------------------------------
-- Description: A multiply and accumulate filter for three inputs
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pkg.all;

entity mac3 is
  generic(
    DATA_WIDTH : integer := 16
    );
  port (
    clk        : in  std_logic;         -- System clock
    rst_n      : in  std_logic;         -- System reset
    sample_clk : in  std_logic;
    -- data
    data_in_1  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    data_in_2  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    data_in_3  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;

architecture arch of mac3 is

  type reg_t is record
    sum : std_logic_vector(DATA_WIDTH-1 downto 0);
  end record;
  
  constant REGISTER_RESET : reg_t := (
    sum => std_logic_vector(to_unsigned(0, DATA_WIDTH))
    );

  signal this, this_nxt : reg_t;

begin

  next_state : process(this, data_in_1, data_in_2, data_in_3, sample_clk)
    variable nxt : reg_t;
  begin
    nxt := this;

    -- defaults
    data_out <= this.sum;

    if sample_clk = '1' then
      nxt.sum := std_logic_vector(resize(
										signed(
											signed(
												(signed(data_in_1)*signed(data_in_1))+
												(signed(data_in_2)*signed(data_in_2))
											)+
											(signed(data_in_3)*signed(data_in_3))
										)
										,DATA_WIDTH
										)
								);
    end if;

    this_nxt <= nxt;
  end process;

  reg : process(clk, rst_n)
  begin
    if rst_n = '0' then
      this <= REGISTER_RESET;
    elsif rising_edge(clk) then
      this <= this_nxt;
    end if;
  end process;

end architecture;
