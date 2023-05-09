FROM ubuntu:18.04 as builder

LABEL maintainer="Gilles Audemard, Laurent Simon"
LABEL version="5.0"
LABEL description="Glucose, a reboot"

RUN apt-get update && apt-get -y upgrade && \
    apt-get -y install apt-utils gcc automake zlib1g-dev make g++ git curl unzip

RUN DEBIAN_FRONTEND=noninteractivei apt-get -y install build-essential software-properties-common

RUN rm -r /var/lib/apt/lists/*

USER root

ADD . /glucose

RUN rm -rf /glucose/pfactory 

RUN curl -L https://github.com/crillab/pfactory/releases/download/v2.0.0/pfactory-2.0.0.zip --output /tmp/pfactory.zip && cd /tmp && unzip pfactory.zip && mv pfactory-2.0.0 /glucose/pfactory && rm -r /tmp/pf*

RUN cd /glucose/pfactory && autoreconf --install && ./configure && make -j

RUN cd /glucose/simp && make rs -j

RUN apt-get update && apt-get install -y linux-tools-`uname -r` linux-tools-generic

#FROM alpine:latest
#RUN mkdir /solver
#COPY --from=builder /glucose/simp/glucose_static /solver/glucose
#RUN ls /solver

ENTRYPOINT ["/solver/glucose"]

#CMD /glucose/simp/glucose
