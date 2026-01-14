from __future__ import annotations
import argparse
import enum
import traceback
from typing import Optional, Callable, Any, TypedDict, Union, NamedTuple
from c2po import log, cpt

class ReturnCode(enum.Enum):
    SUCCESS = 0
    ERROR = 1
    BAG_ARGS = 2
    FILE_NOT_FOUND = 3
    PARSE_ERROR = 4
    REQUIRES_PROGRAM = 5
    GUARD_CONDITION_NOT_MET = 6

class CommandOption(TypedDict):
    """A CommandOption is an option for a command.

    Values:
        - `name`: The name of the option
        - `description`: The description of the option
        - `type`: The type of the option
        - `default`: The default value of the option, optional and will be used if the option is not provided. The type of the default value must be the same as `type`.
        - `choices`: The choices of the option, optional and will be used if the option is provided. The type of the choices must be the same as `type`. If `default` is provided, it must be in `choices`.
    """
    name: str
    description: str
    required: bool
    type: type
    default: Optional[Any]
    choices: Optional[list[Any]]

class CommandGuard(NamedTuple):
    name: str
    predicate: Callable[[cpt.Program, cpt.Context], bool]

VALID_PROGRAM = CommandGuard(name="valid program", predicate=cpt.is_valid_program)
VALID_SIGNAL_MAPPING = CommandGuard(name="valid signal mapping", predicate=cpt.has_valid_signal_mapping)
WELL_TYPED = CommandGuard(name="well-typed", predicate=cpt.is_well_typed_program)
DESUGARED = CommandGuard(name="desugared", predicate=cpt.is_desugared)
VALID_SCQ_SIZES = CommandGuard(name="valid SCQ sizes", predicate=cpt.has_valid_scq_sizes)
COMPUTED_ATOMICS = CommandGuard(name="computed atomics", predicate=cpt.has_computed_atomics)
ONLY_BINARY_OPERATORS = CommandGuard(name="only binary operators", predicate=cpt.is_only_binary_operators)
NO_EXTENDED_OPERATORS = CommandGuard(name="no extended operators", predicate=cpt.has_no_extended_operators)
ASSEMBLED = CommandGuard(name="assembled", predicate=cpt.is_assembled)

# Dependency graph of guard conditions.
GUARD_DEPENDENCIES: dict[CommandGuard, list[CommandGuard]] = {
    VALID_PROGRAM: [],
    VALID_SIGNAL_MAPPING: [],
    WELL_TYPED: [VALID_PROGRAM, VALID_SIGNAL_MAPPING],
    DESUGARED: [WELL_TYPED],
    VALID_SCQ_SIZES: [DESUGARED],
    COMPUTED_ATOMICS: [DESUGARED],
    ONLY_BINARY_OPERATORS: [DESUGARED],
    NO_EXTENDED_OPERATORS: [DESUGARED],
    ASSEMBLED: [DESUGARED, VALID_SCQ_SIZES, COMPUTED_ATOMICS, ONLY_BINARY_OPERATORS, NO_EXTENDED_OPERATORS],
}

class Command:
    """
    A Command is a function that can be executed with a program, context, and options.
    The function can return a boolean indicating success or failure, or an object, which will be added to the interpreter locals.
    For example, a parse command might return a Program object which will be added to the interpreter locals.
    """

    def __init__(
        self,
        name: str,
        description: str,
        options: list[CommandOption] = [],
        func: Callable[
            [cpt.Program, cpt.Context, dict[str, Any]],
            Union[ReturnCode, cpt.Program, None],
        ] = lambda program, context, options: ReturnCode.SUCCESS,
        guards: list[CommandGuard] = [],
    ):
        """Initialize the Command with a name, options, function, guards, and set of commands that are invalidated by this command.

        Args:
            `name`: The name of the command
            `description`: The description of the command
            `options`: List of CommandOptions
            `func`: Function with signature (program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> (ReturnCode | cpt.Program | None)
            `guards`: A list of CommandGuards that must be executed before this command can be executed.
        """
        self.name = name
        self.description = description
        self.options = options
        self.func = func
        self.guards = guards

        self.argparser = argparse.ArgumentParser(prog=name, description=description)
        processed_options = set()
        for option in options:
            if (
                option.get("default") is not None
                and type(option["default"]) is not option["type"]
            ):
                raise ValueError(
                    f"Default value for {option['name']} is not of type {option['type']}: {type(option['default'])}"
                )
            
            if option["name"] in processed_options:
                continue
            processed_options.add(option["name"])

            name = option["name"] if option["required"] else ("--" + option["name"])

            if option["type"] is bool: 
                # All boolean options are optional therefore we use BooleanOptionalAction
                # This allows specifying both "--<name>" and "--no-<name>"
                self.argparser.add_argument(
                    name,
                    help=option["description"],
                    action=argparse.BooleanOptionalAction,
                    default=option["default"],
                )
            elif option["choices"] is not None:
                self.argparser.add_argument(
                    name,
                    help=option["description"],
                    type=option["type"],
                    default=option["default"],
                    choices=option["choices"],
                )
            else:
                self.argparser.add_argument(
                    name,
                    help=option["description"],
                    type=option["type"],
                    default=option["default"],
                )
        
    def check_guards(self, program: cpt.Program, context: cpt.Context) -> Optional[CommandGuard]:
        """Check that the guard conditions are valid for the given program and context.
        Traverse the dependency graph of guard conditions and check that all dependencies are met.
        If any guard condition is not met, return the guard condition that is not met.
        If all guard conditions are met, return None.

        Args:
            `program`: The program to check the guard conditions for
            `context`: The context to check the guard conditions for
        
        Returns:
            The guard condition that is not met if any guard condition is not met, None otherwise.
        """
        # Recursively check all dependencies. No need for iterative approach because the dependency
        # graph is not very deep.
        for guard in self.guards:
            if not guard.predicate(program, context):
                return guard
            for dependency in GUARD_DEPENDENCIES[guard]:
                if not dependency.predicate(program, context):
                    return dependency
        return None

    def parse_args(self, args: list[str]) -> dict[str, Any]:
        return vars(self.argparser.parse_args(args))
        
    def execute(self, program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> Union[ReturnCode, cpt.Program, None]:
        log.debug(1, f"executing {self.name} {self.parsed_options_to_str(options)}")
        log.set_current_command_name(self.name)
        try:
            result = self.func(program, context, options)
            log.reset_current_command_name()
            return result
        except Exception as e:
            log.reset_current_command_name()
            log.internal(f"unexpected error executing {self.name}: {e}", traceback.format_exc())
            return ReturnCode.ERROR

    def __hash__(self) -> int:
        return hash(self.name)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Command):
            return self.name == other.name
        return False

    def parsed_options_to_str(self, options: dict[str, Any]) -> str:
        s = ""
        for option in self.options:
            if option["name"] in options:
                s += f"{option['name']}={options[option['name']]} "
            else:
                s += f"{option['name']}={option['default']} "
        return s

    def __str__(self) -> str:
        return self.name
    
    def __repr__(self) -> str:
        return f"Command(name={self.name}, description={self.description}, options={self.options}, func={self.func})"
    
class CompositeCommand(Command):
    """
    A CompositeCommand is a list of Commands that can be executed in order. 
    All options are passed to every sub-command.
    """
    def __init__(self, name: str, description: str, commands: list[Command], guards: list[CommandGuard]):
        options = [option for command in commands for option in command.options]
        super().__init__(
            name=name,
            description=description,
            options=options,
            func=lambda program, context, options: self.execute(program, context, options),
            guards=guards,
        )
        self.commands = commands

    def execute(self, program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> Union[ReturnCode, Optional[cpt.Program]]:
        """
        Execute the sub-commands in order with short-circuiting.
        `options` are passed to every sub-command. 
        If a sub-command returns None or a ReturnCode other than ReturnCode.SUCCESS, the execution is short-circuited and the result is returned.
        Returns a ReturnCode.SUCCESS if all sub-commands were executed successfully.
        """
        for command in self.commands:
            failed_guard = command.check_guards(program, context)
            if failed_guard is not None:
                log.error(f"guard condition not met for {command.name}: {failed_guard.name}")
                return ReturnCode.GUARD_CONDITION_NOT_MET
            result = command.execute(program, context, options)
            if result is None or result != ReturnCode.SUCCESS:
                return result
        return ReturnCode.SUCCESS

    def __str__(self) -> str:
        return "\n".join([str(command) for command in self.commands])
    
    def __repr__(self) -> str:
        return "\n".join([repr(command) for command in self.commands])

class CommandRegistry:
    """
    A CommandRegistry is a static registry of valid C2PO commands.
    Commands are added to the registry by adding them to the set of valid commands.
    """
    commands: list[Command] = []

    @staticmethod
    def register(command: Command) -> bool:
        """Register a command with the CommandRegistry.

        Args:
            `command`: The command to register

        Returns:
            False if the command already exists, True otherwise.
        """
        if command.name in [command.name for command in CommandRegistry.commands]:
            return False
        CommandRegistry.commands.append(command)
        CommandRegistry.commands.sort(key=lambda x: x.name)
        return True

def set_log_level(options: dict[str, Any]) -> ReturnCode:
    """Command to set the log level.

    `options` is the global options dictionary.
    """
    log.set_log_level(int(options["log_level"]))
    return ReturnCode.SUCCESS

set_log_level_command = Command(
    name="set_log_level",
    description="Set the log level",
    options=[{
        "name": "log_level",
        "description": "The log level",
        "required": True,
        "type": int,
        "default": 0,
        "choices": None,
    }],
    func=lambda program, context, options: set_log_level(options),
    guards=[],
)
CommandRegistry.register(set_log_level_command)

def set_debug() -> ReturnCode:
    log.set_log_level(5)
    return ReturnCode.SUCCESS

set_debug_command = Command(
    name="set_debug",
    description="Set debug (set log level to maximum value)",
    options=[],
    func=lambda program, context, options: set_debug(),
    guards=[],
)
CommandRegistry.register(set_debug_command)

def enable_booleanizer(context: cpt.Context) -> ReturnCode:
    """Command to enable the booleanizer.

    `context` is the context object.
    """
    context.enable_booleanizer = True
    return ReturnCode.SUCCESS

enable_booleanizer_command = Command(
    name="enable_booleanizer",
    description="Enable Booleanizer expressions",
    options=[],
    func=lambda program, context, options: enable_booleanizer(context),
    guards=[],
)
CommandRegistry.register(enable_booleanizer_command)

def disable_booleanizer(context: cpt.Context) -> ReturnCode:
    """Command to disable the booleanizer.

    `context` is the context object.
    """
    context.enable_booleanizer = False
    return ReturnCode.SUCCESS

disable_booleanizer_command = Command(
    name="disable_booleanizer",
    description="Disable Booleanizer expressions",
    options=[],
    func=lambda program, context, options: disable_booleanizer(context),
    guards=[],
)
CommandRegistry.register(disable_booleanizer_command)

def set_mission_time(context: cpt.Context, options: dict[str, Any]) -> ReturnCode:
    """Command to set the mission time.

    `context` is the context object.
    `options` is a dictionary containing the following key:
        - `mission-time`: The mission time
    """
    context.set_mission_time(options["mission-time"])
    return ReturnCode.SUCCESS

set_mission_time_command = Command( 
    name="set_mission_time",
    description="Set the mission time",
    options=[{
        "name": "mission-time",
        "description": "Set the mission time (M variable)",
        "required": True,
        "type": int,
        "default": None,
        "choices": None,
    }],
    func=lambda program, context, options: set_mission_time(context, options),
    guards=[],
)
CommandRegistry.register(set_mission_time_command)

def print_program_c2po(program: cpt.Program) -> ReturnCode:
    print(program)
    return ReturnCode.SUCCESS

print_program_c2po_command = Command(
    name="print_c2po",
    description="Print the C2PO representation of the program",
    options=[],
    func=lambda program, context, options: print_program_c2po(program),
    guards=[],
)
CommandRegistry.register(print_program_c2po_command)

def print_program_mltl(program: cpt.Program, context: cpt.Context) -> ReturnCode:
    print(cpt.to_mltl_std(program, context))
    return ReturnCode.SUCCESS

print_program_mltl_command = Command(
    name="print_mltl",
    description="Print the MLTL representation of the program",
    options=[],
    func=lambda program, context, options: print_program_mltl(program, context),
    guards=[COMPUTED_ATOMICS],
)
CommandRegistry.register(print_program_mltl_command)

def print_program_prefix(program: cpt.Program) -> ReturnCode:
    for spec in program.get_specs():
        print(cpt.to_prefix_str(spec))
    return ReturnCode.SUCCESS

print_program_prefix_command = Command(
    name="print_prefix",
    description="Print the prefix representation each specification in the program",
    options=[],
    func=lambda program, context, options: print_program_prefix(program),
    guards=[],
)
CommandRegistry.register(print_program_prefix_command)
