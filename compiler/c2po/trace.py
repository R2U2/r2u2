

class Trace:

    def __init__(self, trace: list[list[str]]):
        self.trace = trace

    def __str__(self):
        return "\n".join(["\t".join(t) for t in self.trace])

    def __repr__(self):
        return self.__str__()