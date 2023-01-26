import logging

LOGGER_NAME: str = 'c2po_logger'

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

class CustomFormatter(logging.Formatter):

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

logger = logging.getLogger(LOGGER_NAME)
logger.setLevel(logging.DEBUG)

ch = logging.StreamHandler()
ch.setLevel(logging.DEBUG)

ch.setFormatter(CustomFormatter())

logger.addHandler(ch)