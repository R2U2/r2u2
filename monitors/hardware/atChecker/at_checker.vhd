-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : at_checker.vhd
-- Author     : Andreas Hagmann <ahagmann@ecs.tuwien.ac.at>
-- Copyright  : 2012-10, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A single atomic checker block
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.cevLib_unsigned_pkg.all;
use work.at_checker_pkg.all;
use work.math_pkg.all;

entity at_checker is
  generic(
    IN_1_WIDTH : integer := 16;
    IN_2_WIDTH : integer := 16;
    ADDR       : integer := 0
    );
  port (
    clk          : in  std_logic;       -- System clock
    rst_n        : in  std_logic;       -- System reset
    -- config interface
    config_addr  : in  std_logic_vector(3-1 downto 0);
    config_data  : in  std_logic_vector(32-1 downto 0);
    config_write : in  std_logic;
    -- data
    in1          : in  std_logic_vector(IN_1_WIDTH-1 downto 0);
    in2          : in  std_logic_vector(IN_2_WIDTH-1 downto 0);
    ap           : out std_logic
    );
end entity;

architecture arch of at_checker is

  type reg_t is record
    config_c            : std_logic_vector(OP_WIDTH-1 downto 0);
    config_shift_1      : std_logic_vector(log2c(OP_WIDTH)-1 downto 0);
    config_shift_2      : std_logic_vector(log2c(OP_WIDTH)-1 downto 0);
    config_shift_1_sign : std_logic;
    config_shift_2_sign : std_logic;
    config_r_operator   : r_operator_t;
    config_add_operator : a_operator_t;
    in1                 : std_logic_vector(OP_WIDTH-1 downto 0);
    in2                 : std_logic_vector(OP_WIDTH-1 downto 0);
    in1_shifted         : std_logic_vector(OP_WIDTH-1 downto 0);
    in2_shifted         : std_logic_vector(OP_WIDTH-1 downto 0);
    left_result         : std_logic_vector(OP_WIDTH-1 downto 0);
    ap                  : std_logic;
    shift_1             : std_logic_vector(log2c(OP_WIDTH)-1 downto 0);
    shift_2             : std_logic_vector(log2c(OP_WIDTH)-1 downto 0);
    shift_fin           : std_logic;
  end record;
  
  constant REGISTER_RESET : reg_t := (
    (others => '0'),
    (std_logic_vector(to_unsigned(0,log2c(OP_WIDTH)))),--(others => '0'),
    (std_logic_vector(to_unsigned(0,log2c(OP_WIDTH)))),--(others => '0'),
    '0',
    '0',
    GEQ,
    A_ADD,
    (others => '0'),
    (others => '0'),
    (others => '0'),
    (others => '0'),
    (others => '0'),
    '0',
    (std_logic_vector(to_unsigned(0,log2c(OP_WIDTH)))),--(others => '0'),
    (std_logic_vector(to_unsigned(0,log2c(OP_WIDTH)))),--(others => '0'),
    '1'
    );

  signal this, this_nxt : reg_t;

begin

  next_state : process(this, config_write, config_addr, config_data, in1, in2)
    variable nxt        : reg_t;
    variable shift1_fin : std_logic;
    variable shift2_fin : std_logic;
  begin
    nxt := this;

    -- defaults
    shift1_fin := '0';
    shift2_fin := '0';

    ap <= this.ap;

    -- config interface
    if config_write = '1' then
      case config_addr is
        when "000" =>
          nxt.config_c := config_data(nxt.config_c'length-1 downto 0);
        when "001" =>
          nxt.config_shift_1 := config_data(nxt.config_shift_1'length-1 downto 0);
        when "010" =>
          nxt.config_shift_2 := config_data(nxt.config_shift_2'length-1 downto 0);
        when "011" =>
          nxt.config_add_operator := config_data(nxt.config_add_operator'length-1 downto 0);
        when "100" =>
          nxt.config_r_operator := config_data(nxt.config_r_operator'length-1 downto 0);
        when others =>
          null;
      end case;
    end if;

    -- read inputs
    nxt.in1(IN_1_WIDTH-1 downto 0) := in1;
    for i in IN_1_WIDTH to OP_WIDTH-1 loop
      nxt.in1(i) := in1(IN_1_WIDTH-1);  -- sign extension
    end loop;

    nxt.in2(IN_2_WIDTH-1 downto 0) := in2;
    for i in IN_2_WIDTH to OP_WIDTH-1 loop
      nxt.in2(i) := in2(IN_2_WIDTH-1);  -- sign extension
    end loop;

    -- shift values
    if this.shift_fin = '1' then
      nxt.shift_fin   := '0';
      nxt.shift_1     := this.config_shift_1;
      nxt.shift_2     := this.config_shift_2;
      nxt.in1_shifted := this.in1;
      nxt.in2_shifted := this.in2;
    else
      -- shift 1
      if this.shift_1 /= std_logic_vector(to_unsigned(0, this.shift_1'length)) then
        if this.config_shift_1_sign = '1' then  -- shift right
          nxt.in1_shifted := '0' & this.in1_shifted(OP_WIDTH-1-1 downto 0);
        else                                    -- shift left
          nxt.in1_shifted := this.in1_shifted(OP_WIDTH-1 downto 1) & '0';
        end if;
        nxt.shift_1 := this.shift_1 - 1;
      else
        shift1_fin := '1';
      end if;

      -- shift 2
      if this.shift_2 /= std_logic_vector(to_unsigned(0, this.shift_2'length)) then
        if this.config_shift_2_sign = '1' then  -- shift right
          nxt.in2_shifted := '0' & this.in2_shifted(OP_WIDTH-1-1 downto 0);
        else                                    -- shift left
          nxt.in2_shifted := this.in2_shifted(OP_WIDTH-1 downto 1) & '0';
        end if;
        nxt.shift_2 := this.shift_2 - 1;
      else
        shift2_fin := '1';
      end if;

      if shift1_fin = '1' and shift2_fin = '1' then
        nxt.shift_fin := '1';
      end if;
    end if;

    -- add / sub
    if this.shift_fin = '1' then
      case this.config_add_operator is
        when A_ADD =>
          nxt.left_result := std_logic_vector(unsigned(this.in1_shifted) + unsigned(this.in2_shifted));
        when A_SUB =>
          nxt.left_result := std_logic_vector(unsigned(this.in1_shifted) - unsigned(this.in2_shifted));
        when A_DIF =>
          if(unsigned(this.in1_shifted)>unsigned(this.in2_shifted))then
            nxt.left_result := std_logic_vector(unsigned(this.in1_shifted) - unsigned(this.in2_shifted));
          else
            nxt.left_result := std_logic_vector(unsigned(this.in2_shifted) - unsigned(this.in1_shifted));
          end if;
        when others =>
          null;
      end case;
    end if;

    -- compare
    case this.config_r_operator is
      when GEQ =>
        if signed(this.left_result) >= signed(this.config_c) then
          nxt.ap := '1';
        else
          nxt.ap := '0';
        end if;
        
      when LEQ =>
        if signed(this.left_result) <= signed(this.config_c) then
          nxt.ap := '1';
        else
          nxt.ap := '0';
        end if;
        
      when GRE =>
        if signed(this.left_result) > signed(this.config_c) then
          nxt.ap := '1';
        else
          nxt.ap := '0';
        end if;
        
      when LES =>
        if signed(this.left_result) < signed(this.config_c) then
          nxt.ap := '1';
        else
          nxt.ap := '0';
        end if;
        
      when NEQ =>
        if signed(this.left_result) /= signed(this.config_c) then
          nxt.ap := '1';
        else
          nxt.ap := '0';
        end if;
        
      when EQU =>
        if signed(this.left_result) = signed(this.config_c) then
          nxt.ap := '1';
        else
          nxt.ap := '0';
        end if;
        
      when others =>
        null;
        
    end case;

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
