-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : rate.vhd
-- Author     : Andreas Hagmann <ahagmann@ecs.tuwien.ac.at>
-- Copyright  : 2012-10, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A rate Filter
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pkg.all;

entity rate is
  generic(
    DATA_WIDTH : integer := 16
    );
  port (
    clk        : in  std_logic;         -- System clock
    rst_n      : in  std_logic;         -- System reset
    sample_clk : in  std_logic;
    -- data
    data_in    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    data_out   : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;

architecture arch of rate is

  type reg_t is record
    last_in : std_logic_vector(DATA_WIDTH-1 downto 0);
    rate    : std_logic_vector(DATA_WIDTH-1 downto 0);
  end record;
  
  constant REGISTER_RESET : reg_t := (
    (std_logic_vector(to_unsigned(0, DATA_WIDTH))),  --(others => '0'),
    (std_logic_vector(to_unsigned(0, DATA_WIDTH)))   --  (others => '0')
    );

  signal this, this_nxt : reg_t;

begin

  next_state : process(this, data_in, sample_clk)
    variable nxt : reg_t;
  begin
    nxt := this;

    -- defaults

    data_out <= this.rate;

    if sample_clk = '1' then
      nxt.rate    := std_logic_vector(signed(data_in) - signed(this.last_in));
      nxt.last_in := data_in;
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
