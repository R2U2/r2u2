-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : lowpass.vhd
-- Author     : Andreas Hagmann <ahagmann@ecs.tuwien.ac.at>
-- Copyright  : 2012-10, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A maximum Filter
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pkg.all;

entity max is
  generic(
    DATA_WIDTH : integer := 16
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

architecture arch of max is

  type reg_t is record
	max			: std_logic_vector(DATA_WIDTH-1 downto 0);
  end record;
  
  constant REGISTER_RESET : reg_t := (
    max => (others => '0')
  );

  signal this, this_nxt : reg_t;

begin

  next_state : process(this, data_in, sample_clk)
    variable nxt : reg_t;
  begin
    nxt := this;
    
    -- defaults
    
    data_out <= this.max;
    
    if sample_clk = '1' then
   
   		if signed(data_in) > signed(this.max) then
			nxt.max := data_in;
		end if; 
	
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