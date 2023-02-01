from io import StringIO
import logging
import sys

STANDARD_LOGGER_NAME: str = 'c2po_standard_logger'
COLOR_LOGGER_NAME: str = 'c2po_color_logger'

class Color:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

class StandardFormatter(logging.Formatter):

    format_str = '%(levelname)s'

    FORMATS = {
        logging.DEBUG: format_str + ':%(message)s',
        logging.INFO: format_str + ':%(message)s',
        logging.WARNING: format_str + ':%(message)s',
        logging.ERROR: format_str + ':%(message)s',
        logging.CRITICAL: format_str + ':%(message)s',
    }

    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)

class ColorFormatter(logging.Formatter):

    format_str = '%(levelname)s'

    FORMATS = {
        logging.DEBUG: Color.BOLD + Color.OKBLUE + format_str + Color.ENDC + ':%(message)s',
        logging.INFO: Color.BOLD + Color.OKCYAN + format_str + Color.ENDC + ':%(message)s',
        logging.WARNING: Color.BOLD + Color.WARNING + format_str + Color.ENDC + ':%(message)s',
        logging.ERROR: Color.BOLD + Color.FAIL + format_str + Color.ENDC + ':%(message)s',
        logging.CRITICAL: Color.BOLD + Color.FAIL + format_str + Color.ENDC + ':%(message)s',
    }

    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)


standard_logger = logging.getLogger(STANDARD_LOGGER_NAME)
standard_logger.setLevel(logging.DEBUG)

log_stream = StringIO()
standard_logger_handler = logging.StreamHandler(log_stream)
standard_logger_handler.setLevel(logging.ERROR)

standard_logger_handler.setFormatter(StandardFormatter())

standard_logger.addHandler(standard_logger_handler)


color_logger = logging.getLogger(COLOR_LOGGER_NAME)
color_logger.setLevel(logging.DEBUG)

color_logger_handler = logging.StreamHandler(log_stream)
color_logger_handler.setLevel(logging.DEBUG)

color_logger_handler.setFormatter(ColorFormatter())

color_logger.addHandler(color_logger_handler)