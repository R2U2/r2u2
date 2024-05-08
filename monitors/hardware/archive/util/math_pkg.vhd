------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : math_pkg.vhd
-- Author     : Daniel Schachinger
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: Some useful mathematical functions                                  
-------------------------------------------------------------------------------
use work.cevLib_unsigned_pkg.all;

package math_pkg is

  -- calculates the logarithm dualis of the operand and rounds up
  -- the result to the next integer value.
  function log2c(constant value                        : in integer) return integer;
  -- returns the maximum of the two operands
  -- function max(constant value1, value2                 : in integer) return integer;
  -- returns the maximum of the three operands
  function max(constant value1, value2, value3         : in integer) return integer;
  -- returns the maximum of the four operands
  function max(constant value1, value2, value3, value4 : in integer) return integer;
  -- function minimum (constant value1, value2            : in integer) return integer;
  -- function condAssign(b : boolean; V1 : integer; V2 : integer) return integer;
  function divceil(constant value1, value2             : in natural) return natural;

end math_pkg;

package body math_pkg is

  --  function condAssign(b : boolean; V1 : integer; V2 : integer) return integer is
  --  variable result : integer;
  --begin
  --  if b = true then
  --    result := V1;
  --  else
  --    result := V2;
  --  end if;
  --  return result;
  --end function condAssign;

  -- logarithm dualis
  function log2c(constant value : in integer) return integer is
    variable ret_value : integer;
    variable cur_value : integer;
  begin
    ret_value := 0;
    cur_value := 1;

    while cur_value < value loop
      ret_value := ret_value + 1;
      cur_value := cur_value * 2;
    end loop;
    return ret_value;
  end function log2c;

  -- maximum of two operands
  --function max(constant value1, value2 : in integer) return integer is
  --  variable ret_value : integer;
  --begin
  --  if value1 > value2 then
  --    ret_value := value1;
  --  else
  --    ret_value := value2;
  --  end if;
  --  return ret_value;
  --end function max;

  -- maximum of three operands
  function max(constant value1, value2, value3 : in integer) return integer is
  begin
    return max(max(value1, value2), value3);
  end function max;
  -- maximum of four operands
  function max(constant value1, value2, value3, value4 : in integer) return integer is
  begin
    return max(max(value1, value2), max(value3, value4));
  end function max;

  --function minimum(constant value1, value2 : in integer) return integer is
  --  variable ret_value : integer;
  --begin
  --  if value1 < value2 then
  --    ret_value := value1;
  --  else
  --    ret_value := value2;
  --  end if;
  --  return ret_value;
  --end function;

  function divceil(constant value1, value2 : in natural) return natural is
    variable divcounter : natural := 0;
    variable remainder  : integer := value1;
  begin
-- Patrick 2/11/15 Fix in Math library
-- Prior    while remainder >= value2 loop
    while remainder >= (value2+1) loop
      remainder  := remainder - value2;
      divcounter := divcounter + 1;
    end loop;
    return divcounter+1;
  end function divceil;
  
  
end package body math_pkg;
