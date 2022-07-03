import logging

logger_name: str = 'c2po_logger'

class colors:
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
        logging.DEBUG: colors.BOLD + colors.OKBLUE + format_str + colors.ENDC + ':%(message)s',
        logging.INFO: colors.BOLD + colors.OKCYAN + format_str + colors.ENDC + ':%(message)s',
        logging.WARNING: colors.BOLD + colors.WARNING + format_str + colors.ENDC + ':%(message)s',
        logging.ERROR: colors.BOLD + colors.FAIL + format_str + colors.ENDC + ':%(message)s',
        logging.CRITICAL: colors.BOLD + colors.FAIL + format_str + colors.ENDC + ':%(message)s',
    }

    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)

logger = logging.getLogger(logger_name)
logger.setLevel(logging.DEBUG)

ch = logging.StreamHandler()
ch.setLevel(logging.DEBUG)

ch.setFormatter(CustomFormatter())

logger.addHandler(ch)