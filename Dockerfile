FROM alpine:latest

RUN apk add --no-cache make gcc g++ musl-dev binutils bash
RUN apk add --no-cache python3 py3-pip py3-numpy py3-matplotlib
RUN pip install dash dash-cytoscape dash-bootstrap-components pytest

ENV HOME=/home
WORKDIR $HOME
COPY . .

EXPOSE 8050

CMD ["/bin/bash"]

