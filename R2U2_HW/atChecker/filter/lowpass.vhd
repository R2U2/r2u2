-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : lowpass.vhd
-- Author     : Andreas Hagmann <ahagmann@ecs.tuwien.ac.at>
-- Copyright  : 2012-10, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A exponential IIR Filter
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pkg.all;

entity lowpass is
  generic(
    DATA_WIDTH : integer := 16;
    FILTER_WEIGHT : integer := 1;
    FILTER_LEN : integer := 8
  );
  port (
    clk             : in  std_logic;    -- System clock
    rst_n           : in  std_logic;    -- System reset
    sample_clk		: in  std_logic;
    -- data
    data_in         : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    data_out        : out std_logic_vector(DATA_WIDTH-1 downto 0)
  );
end entity;

architecture arch of lowpass is

  type reg_t is record
	y			: std_logic_vector(DATA_WIDTH-1 downto 0);
  end record;
  
  constant REGISTER_RESET : reg_t := (
    y => (others => '0')
  );

  signal this, this_nxt : reg_t;

begin

  next_state : process(this, data_in, sample_clk)
    variable nxt : reg_t;
  	variable accu : std_logic_vector(DATA_WIDTH+log2c(FILTER_LEN)+1-1 downto 0);
  begin
    nxt := this;
    
    -- defaults
    
    data_out <= this.y;
    accu := std_logic_vector(signed(this.y) * to_signed((FILTER_LEN - FILTER_WEIGHT), log2c(FILTER_LEN+1)) + signed(data_in) * to_signed(FILTER_WEIGHT, log2c(FILTER_LEN+1)));
    --accu := std_logic_vector(signed(data_in) * to_signed(FILTER_LEN - FILTER_WEIGHT, log2c(FILTER_LEN+1)));
   	if sample_clk = '1' then
		nxt.y := accu(DATA_WIDTH+log2c(FILTER_LEN)-1 downto log2c(FILTER_LEN));
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