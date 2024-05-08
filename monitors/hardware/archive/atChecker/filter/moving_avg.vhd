-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : moving_avg.vhd
-- Author     : Andreas Hagmann <ahagmann@ecs.tuwien.ac.at>
-- Copyright  : 2012-10, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A moving avgimum Filter
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pkg.all;
use work.cevLib_unsigned_pkg.all;
use work.ram_pkg.all;

entity moving_avg is
  generic(
    DATA_WIDTH : integer := 16;
    FILTER_LEN : integer := 64
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

architecture arch of moving_avg is

  type reg_t is record
	avg			: std_logic_vector(DATA_WIDTH-1 downto 0);
	sum			: std_logic_vector(DATA_WIDTH+log2c(FILTER_LEN)-1 downto 0);
	write_pointer : std_logic_vector(log2c(FILTER_LEN)-1 downto 0);
  end record;
  
  constant REGISTER_RESET : reg_t := (
    (others => '0'),
    (others => '0'),
    (others => '0')
  );

  signal write : std_logic;
  signal read_data : std_logic_vector(DATA_WIDTH-1 downto 0);
  
  signal this, this_nxt : reg_t;
begin
    
  -- buffer
  iram : sp_ram_wt 
    generic map (
		ADDR_WIDTH       => log2c(FILTER_LEN),
		DATA_WIDTH       => DATA_WIDTH)     	
	port  map (
		clk              => clk,
		addr             => this.write_pointer,
		write            => write,          
		wrData           => data_in,
		rdData           => read_data);
		
  next_state : process(this, data_in, sample_clk)
    variable nxt : reg_t;
  begin
    nxt := this;
    
    -- defaults
    write <= '0';
    data_out <= this.sum(DATA_WIDTH+log2c(FILTER_LEN)-1 downto log2c(FILTER_LEN));
    
    if sample_clk = '1' then
		write <= '1'; 
		nxt.sum := std_logic_vector(signed(this.sum) + signed(data_in) - signed(read_data));
		nxt.write_pointer := this.write_pointer + 1;
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
