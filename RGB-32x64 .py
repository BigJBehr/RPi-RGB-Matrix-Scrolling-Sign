#!/usr/bin/env python

# Author:  James R. Behrens
# Project: Rasperry Pi RGB 32x64 Scrolling display
# Target:  Stretch Lite running on a Raspberry Pi Zero W.

# This is a Python script that drives a 32x64 matrix of RGB LEDs. The RGB matrix
# panel uses a Hub75 interface.
# The Python script divides the 32x64 panel into two lines of text. Each line
# displays different information gathered from the Internet and from some local
# XML files. An INI file determines which features are enabled and provides the
# URLs for some of the Internet sites.
# A BME280 environmental sensor array provides in-house temperature, humidity
# and barometric pressure.

# The display is two 32x32 matrices on one board. Run with;
# sudo python RGB-32x64.py

# default matrix size in samplebase.py was changed to 32x64 from 32x32. This
# eliminated the need to add '-c 2' to the command line.'

# This script was adapted from one of the example programs that are included with
# the Henner Zeller LED-matrix library. The library is (c) Henner Zeller
# <h.zeller@acm.org>, licensed with GNU General Public License Version 2.0]
# (http://www.gnu.org/licenses/gpl-2.0.txt)(which means, if you use it in a
# product somewhere, you need to make the source and all your modifications
# available to the receiver of such product so that they have the freedom to
# adapt and improve). The driver library itself has not been modified. You can
# obtain the library from; https://github.com/hzeller/rpi-rgb-led-matrix.
# Read the README.md file. Follow the directions for installation and for
# eliminating interference from the 'snd_bcm2835' driver.

# this will prevent snd_bcm2835 driver from being loaded.
# the prompt should be similar to this; pi@StretchLite:~ $
# type; cat <<EOF | sudo tee /etc/modprobe.d/blacklist-rgb-matrix.conf
# the prompt will change to >
# type; blacklist snd_bcm2835
# type; EOF
# the prompt changes back to pi@StretchLite:~ $
# type; sudo update-initramfs -u

# reboot your Pi
# type; sudo reboot

# after the reboot
# type; lsmod
# look for snd_bcm2835. if it is present then try again. You should not see
# snd_bcm2835 when you type; lsmod


# This project uses the default, single display HUB75 interface wiring. Board
# layouts are provided with the library. AdaFruit has a compatible HAT.
# I created my own Raspberry Pi Hub75 interface board that breaks out the
# unused GPIO pins to a header. The I2C and console pins are also broken out
# to their own headers. Level shifters are incorporated for all pins that
# connect to the display. A jumper is provided for 16 or 32 row selection. An 
# optional 3.3V regulator was added to power any external addons.

# create a directory for this project
# mkdir /home/pi/rgb-32x64

# use WinSCP to copy the project files to the rgb-32x64 directory

# compile and install the Henner Zeller RGB LED Matrix library
# type; cd rpi-rgb-led-matrix-master/bindings/python
# type; sudo apt-get update && sudo apt-get install python2.7-dev python-pillow -y
# type; sudo make build-python
# type; sudo make install-python


# type; sudo python setup.py install
# type; cd ..
# type; cd ..
# type; cd ..




# All of the following must be in the same directory as 'RGB-32x64.py';
# 'fonts' directory, 'samplebase.py', 'birthdays.xml', 'holidays.xml' and
# 'options.ini'.
#
# This project needs some python libraries installed. At the Linux command
# prompt type the following commands to install the required libraries;

# Install pip. pip is used to install Python libraries.
# sudo apt-get install python-pip

# install smbus library
# type sudo apt-get install python-smbus

# install Python requests library
# type; sudo apt-get install python-requests


# To run on power up, edit /etc/rc.local to add the following two lines just
# above the 'exit 0' line;
# type; cd /home/pi/rgb-32x64
# type; sudo python RGB-32x64.py

# Change permissions of rc.local so you can edit it, type
# type; chmod 777 /etc/rc.local

# rc.local should be executable. If not type;
# type; /etc/rc.local enabled

# message lists are lists of lists. each entry is a list with two values, text color
# and the text to display.

# changed to do one url at a time for headlines, like jokes does.


# Display a runtext with double-buffering.
import datetime
import time
import thread
import threading
import calendar
import decimal
import os.path
import json
import requests
import htmlentitydefs
import gc
import sys
import socket
import struct
import string
import random

from HTMLParser import HTMLParser
from xml.dom import minidom
from socket import AF_INET, SOCK_DGRAM
from samplebase import SampleBase
from rgbmatrix import graphics
from smbus import SMBus

# sensor data variables
lastPressure = 0
Barometer = 0

# create an SMBUS (I2C) object, use bus 1, bus 0 is reserved
Bme = SMBus(1)
  
lastDow       = 0

# dirtyFlag is used to indicate when a new bottomList needs to be built
dirtyFlag     = True

# dirtyLock is used to prevent multiple threads from accessing various lists
# at the same time. simple thread protectiom mechanism
dirtyLock     = threading.Lock()

topIndex      = 0
bottomIndex   = 0

jokesIndex    = 0

topList     = []
bottomList  = []

# using separate lists makes it easier to update sensor & weather messages
# without having to re-build other lists
sensorList  = []
dailyList   = []
weatherList = []
quoteList   = []
jokeList    = []
newsList    = []

##### options, these are read in from the options.ini file on startup #####
militaryTime = False

#..BME280 sensor enables
temperature  = True
humidity     = True
pressure     = True

weatherEnabled = False
weatherKey     = ''
weatherZip     = ''

quoteEnabled = False
quoteUrl     = ''

jokesEnabled = False
jokesUrls    = []
jokesDelay   = 3600

newsEnabled  = False
newsUrls     = []


# bottom row of font. leave two below for decenders
Row1 = 11
Row2 = 28

#===== BME280 Calibration Data Storage =====
digT1 = 0     # temperature compensation data
digT2 = 0
digT3 = 0

digP1 = 0    # humidity compensation data
digP2 = 0
digP3 = 0
digP4 = 0
digP5 = 0
digP6 = 0
digP7 = 0
digP8 = 0
digP9 = 0

digH1 = 0    # pressure compensation data
digH2 = 0
digH3 = 0
digH4 = 0
digH5 = 0
digH6 = 0

#===== BME280 Register names, do not modify =====
BME280_DIG_T1_LSB_REG =	0x88
BME280_DIG_T1_MSB_REG =	0x89
BME280_DIG_T2_LSB_REG =	0x8A
BME280_DIG_T2_MSB_REG =	0x8B
BME280_DIG_T3_LSB_REG =	0x8C
BME280_DIG_T3_MSB_REG =	0x8D
BME280_DIG_P1_LSB_REG =	0x8E
BME280_DIG_P1_MSB_REG =	0x8F
BME280_DIG_P2_LSB_REG =	0x90
BME280_DIG_P2_MSB_REG =	0x91
BME280_DIG_P3_LSB_REG =	0x92
BME280_DIG_P3_MSB_REG =	0x93
BME280_DIG_P4_LSB_REG =	0x94
BME280_DIG_P4_MSB_REG =	0x95
BME280_DIG_P5_LSB_REG =	0x96
BME280_DIG_P5_MSB_REG =	0x97
BME280_DIG_P6_LSB_REG =	0x98
BME280_DIG_P6_MSB_REG =	0x99
BME280_DIG_P7_LSB_REG =	0x9A
BME280_DIG_P7_MSB_REG =	0x9B
BME280_DIG_P8_LSB_REG =	0x9C
BME280_DIG_P8_MSB_REG =	0x9D
BME280_DIG_P9_LSB_REG =	0x9E
BME280_DIG_P9_MSB_REG =	0x9F
BME280_DIG_H1_REG           =	0xA1
BME280_CHIP_ID_REG          =	0xD0 # Chip ID
BME280_RST_REG              =	0xE0 # Softreset Reg
BME280_DIG_H2_LSB_REG       =	0xE1
BME280_DIG_H2_MSB_REG       =	0xE2
BME280_DIG_H3_REG           =	0xE3
BME280_DIG_H4_MSB_REG       =	0xE4
BME280_DIG_H4_LSB_REG       =	0xE5
BME280_DIG_H5_MSB_REG       =	0xE6
BME280_DIG_H6_REG           =	0xE7
BME280_CTRL_HUMIDITY_REG    =	0xF2 # Ctrl Humidity Reg
BME280_STAT_REG             =	0xF3 # Status Reg
BME280_CTRL_MEAS_REG        =	0xF4 # Ctrl Measure Reg
BME280_CONFIG_REG           =	0xF5 # Configuration Reg
BME280_PRESSURE_MSB_REG     =	0xF7 # Pressure MSB
BME280_PRESSURE_LSB_REG     =	0xF8 # Pressure LSB
BME280_PRESSURE_XLSB_REG    = 0xF9 # Pressure XLSB
BME280_TEMPERATURE_MSB_REG  = 0xFA # Temperature MSB
BME280_TEMPERATURE_LSB_REG  = 0xFB # Temperature LSB
BME280_TEMPERATURE_XLSB_REG =	0xFC # Temperature XLSB
BME280_HUMIDITY_MSB_REG     =	0xFD # Humidity MSB
BME280_HUMIDITY_LSB_REG     =	0xFE # Humidity LSB

BMEADRS =	0x76        # I2C address of the BME280
BME280_CHIP_ID = 0x60 # chip ID of the BME280

UNSIGNED = 0
SIGNED = 1


#==============================================================================
# return True if the string afer '=' starts with 't' or 'T' otherwise return
# false
def truefalse(str):
  s = str[0].lower()
  return 't' == s
    
#==============================================================================
# Read the options file into memory. Options 
# read options.ini into global vars
def readOptions(filename):
  global military

  global temperature
  global humidity
  global pressure

  global weatherEnabled
  global weatherKey
  global weatherZip
  
  global quoteEnabled
  global quoteUrl
  
  global jokesEnabled
  global jokesUrls
  global jokesDelay

  global newsEnabled
  global newsUrls
    
  if os.path.isfile(filename):
    try:
      with open(filename, 'r') as f:
        print "Reading options file"
        for line in f:
          if len(line) > 2:
            # split on the first '=' only
            s = line[:len(line) - 1].split('=', 1)
            # remove trailing '\n'
            value = s[1][:len(s[1]) - 1]
            
            if s[0] == 'military':
              military = truefalse(value)
            elif s[0] == 'temperature':
              temperature = truefalse(value)
            elif s[0] == 'humidity':
              humidity = truefalse(value)
            elif s[0] == 'pressure':
              pressure = truefalse(value)
            elif s[0] == 'weather':
              weatherEnabled = truefalse(value)
            elif s[0] == 'weatherkey':
              weatherKey = value
            elif s[0] == 'weatherzip':
              weatherZip = value
            elif s[0] == 'quote':
              quoteEnabled = truefalse(value)
            elif s[0] == 'quoteurl':
              # we may have a list of urls to get jokes from
              quoteUrl = value
            elif s[0] == 'jokes':
              jokesEnabled = truefalse(value)
            elif s[0] == 'jokesurl':
              # there are multiple joke URLs. each for a differnt type of joke
              jokesUrls.append(value)
            elif s[0] == 'jokedelay':
              jokesDelay = int(value)
            elif s[0] == 'news':
              newsEnabled = truefalse(value)
            elif s[0] == 'newsurl':
              # there may be multiple news feeds used
              # there maybe multiple '=' in the url
              newsUrls.append(value)
    except IOError:
      print "Failure reading options file"
  else:
    print "Unable to find options.ini file"
                        
#==============================================================================
# Create a random color
def randomColor():
  min = 64      # higher numbers yield brighter colors, max is 255
  max = 255     # low numbers yield dimmer colors.
  
  r = random.randint(min, max)
  g = random.randint(min, max)
  b = random.randint(min, max)
  return graphics.Color(r, g, b)

#==============================================================================
# get the current Internet time from an NTP server
def getNTPTime(host = "pool.ntp.org"):
  port = 123
  buf = 1024
  address = (host, port)
  msg = '\x1b' + 47 * '\0'
  
  # reference time (in seconds since 1900-01-01 00:00:00)
  TIME1970 = 2208988800L # 1970-01-01 00:00:00
  
  # connect to server
  client = socket.socket(AF_INET, SOCK_DGRAM)
  client.sendto(msg, address)
  msg, address = client.recvfrom(buf)
  
  t = struct.unpack("!12I", msg)[10]
  t -= TIME1970
  return time.ctime(t).replace("  "," ")
  
#==============================================================================
# create a date message
# this is run while the dirtyLock has been acquired, so safe to change dailyList
# xml files must be in same directory as executable

def dateMessage():
  global lastDow
     
  dow = datetime.datetime.today()
  dayname = calendar.day_name[dow.weekday()]
  text = dayname + ", " + datetime.datetime.now().strftime("%b %d %Y")

  # check for change of dow, signals new day
  if lastDow != dow.weekday():
    print 'New Day' + str(dow.weekday()) + ', ' + str(lastDow)
    del dailyList[:]
    loadFromXml("holidays.xml",  str(datetime.datetime.now().month), str(datetime.datetime.now().day), dayname)
    loadFromXml("birthdays.xml", str(datetime.datetime.now().month), str(datetime.datetime.now().day), dayname)
  
  lastDow = dow.weekday()
  return text

#==============================================================================
# create time msg
# this is run while the dirtyLock has been acquired

def timeMessage():
  global militaryTime
  
  if militaryTime == False:
    h = datetime.datetime.now().hour
    if h > 12:
      h -= 12
        
    if 0 == h:
      h = 12

    text = '{:2d}:{:02d}:{:02d}'.format(h, datetime.datetime.now().minute, datetime.datetime.now().second)
  else:
    text = datetime.datetime.now().strftime("%H:%M")

  return text
             
#==============================================================================
# Class to strip HTML tags from strings.

class HTMLTextExtractor(HTMLParser):
  def __init__(self):
    HTMLParser.__init__(self)
    self.result = [ ]

  def handle_data(self, d):
    self.result.append(d)

  def handle_charref(self, number):
    codepoint = int(number[1:], 16) if number[0] in (u'x', u'X') else int(number)
    self.result.append(unichr(codepoint))

  def handle_entityref(self, name):
    codepoint = htmlentitydefs.name2codepoint[name]
    self.result.append(unichr(codepoint))

  def get_text(self):
     return u''.join(self.result)

#==============================================================================
# Remove HTML tags from a string.
def html_to_text(html):
  s = HTMLTextExtractor()
  s.feed(html)
  return s.get_text()
    
#==============================================================================
# Get a joke from the Internet. Parse out the joke and author. There may be
# multiple joke URLs. Use a different URL each time this is invoked.
def getAJoke():
  global jokeList
  global jokeUrls
  global dirtyFlag
  global jokesIndex
  global jokesDelay
  
  list   = []  
  while True:
    # try to get a new joke
    try:
      r = requests.get(jokesUrls[jokesIndex])
    except:
      print 'Jokes, invalid URL: {}'.format(jokesUrls[jokesIndex])
    finally:
      if 200 == r.status_code:
        # parse the joke from the HTML pages. the parsed text is combined into
        # one long string and then broken down into displayable pieces.
  
        flag   = 0
        joke   = ''
        author = ''
  
        color = randomColor()             
        # split the HTML into lines
        lines = r.text.splitlines()
       
        for line in lines:
          if 0 == flag:
            if '<P>' == line:
              flag = 1

          elif 1 == flag:
            if '<CENTER>' == line:
              flag = 2

 # this caused an issue when non-joke text was processed. contained non-ascii 
 # characters             
            else:
              # strip HTML. convert to ASCII and remove all leading and trailing
              # whitespace
              line1 = html_to_text(line).strip().encode('ascii')
              if len(line1) > 0:
                # remove spaces and dashes
                line1 = line1.strip('- ')
                joke += ' ' + line1
                if joke.endswith('?') or joke.endswith('.'):
                  list.append([color, joke])
                  joke = ''
        # for
        
        # we found a joke.
        if len(joke) > 0:
          list.append([color, joke])

        if len(list) > 0:
          dirtyLock.acquire()
          del jokeList[:]
          dirtyFlag = True
          jokeList += list
          dirtyLock.release()
          del list[:]
        else:
          print 'No joke from: ' + jokesUrls[jokesIndex]
          
        # we may have several joke URLs. step through them one at a time.
        jokesIndex += 1
        if jokesIndex == len(jokesUrls):
          jokesIndex = 0
  
      else:
        print 'Get a Joke Failed to connect'

      
    # sleep for some number of seconds
    time.sleep(jokesDelay)
  # while    
        
#==============================================================================
# Get the Quote-of-the-day. Parse out the quote and author. Add it to the 
# quoteList.
def getQuoteOfTheDay():
  global quoteList
  global dirtyFlag
  
  quote = []
  ql = []
  delay = 3600        # update once an hour
  while True:
    try:
      print 'QOD Thread'
      r = requests.get(quoteUrl, auth=('user', 'pass'))
      if 200 == r.status_code:
#        print '===== QOD ====='
#        print r.text
#        print '====='
        # split into individual lines
        list = r.text.splitlines()
              
        for l in list:
#          print l
          # only interested in lines that start with 'br.writeln'
          if l.startswith('br.writeln'):
            # strip off the first 12 characters
            s = l[12:]
            # nothing of interest starts with '<b'
            if not s.startswith('<b'):
              # parse the quote. quote ends with '<br>'
              if s.endswith('<br>");'):
                quote.append(s[:s.find('<br>')])
              
              # parse the author.
              pos = s.find('</a>')
              if pos > 0:
                quote.append(s[s.find('>') + 1:pos])
  
        if len(quote) > 0:
          color = randomColor()
          if len(quote[0]) > 0:
            ql.append([color, quote[0]])
    
            # add the author
            if len(quote[1]) > 0:
              ql.append([color, quote[1]])
          else:
            # no quote given
            print 'No quote found'
        else:
          # no quote given
          print 'No quote found'
            
      else:
        print 'Quote of the Day returned an error: ' + str(r.status_code)
  
    except:
      print "Quote of the day failed to connect"
      
      # use default quote
      color = randomColor()
      ql.append([color, 'Progress is impossible without change, and those who cannot change their minds cannot change anything'])
      ql.append([color, 'George Bernard Shaw'])
    # try/except
        
    dirtyLock.acquire()
    del quoteList[:]
    dirtyFlag = True
    print 'Quote of the Day'
    quoteList += ql
    dirtyLock.release()
    del ql[:]
    del quote[:]
    
    # sleep for some number of seconds
    time.sleep(delay)
  # while

#==============================================================================
# Get the current weather from OpenWeatherMap.org
def getWeather():
  global weather
  global weatherKey
  global weatherZip
  global weatherList
  global dirtyFlag
    
  list = []
  delay = 900       # update every 15 minutes
  
  print 'Get Weather'
  
  weather = ''
  temperature = 0.0
  pressure = 0.0
  humidity = 0.0
  windspeed = 0.0
  winddir = 0
  windgust = 0.0
  
  while True:
    print 'Updating weather information'
    
    try:
      url = 'http://api.openweathermap.org/data/2.5/weather?zip={}&APPID={}'.format(weatherZip, weatherKey)
      r = requests.get(url)
    except:
      # this occurs when we cannot connect to the OpenWeatherMap service    
      print 'Unable to connect to OpenWeatherMap.org, Key or Zipcode may be invalid'

    # parse the weather data
    if 200 == r.status_code:
      print 'Parsing Weather info'
      # parse the weather information
#      print '====='
#      print r.text
#      print '====='
      wlist = r.text.split(',')
      for l in wlist:
#        print l
        pos = l.find('description":"')
        if pos > 0:
          weather = l[l.find(':') + 2:len(l) - 1]
    
        pos = l.find('temp":')
        if pos > 0:
          temperature = float(l[pos + 6:])
          
        pos = l.find('pressure":')
        if pos > 0:
          pressure = float(l[l.find(':') + 1:])
              
        pos = l.find('humidity":')
        if pos > 0:
          humidity = float(l[l.find(':') + 1:])
              
        pos = l.find('speed":')
        if pos > 0:
          windspeed = float(l[l.rfind(':') + 1:])
          
        pos = l.find('deg":')
        if pos > 0:
          l = l.strip('}')
          winddir = float(l[l.find(':') + 1:])
          
        pos = l.find('gust":')
        if pos > 0:
          windgust = float(l[l.find(':') + 1:len(l) - 1])
      # for
    
      # convert wind direction in degrees to text direction
      if winddir < 22.5:
          wdt = "North"
      elif winddir < 67.5:
          wdt = "Northeast"
      elif winddir < 112.5:
          wdt = "East"
      elif winddir < 157.5:
          wdt = "Southeast"
      elif winddir < 202.5:
          wdt = "South"
      elif winddir < 247.5:
          wdt = "Southwest"
      elif winddir < 292.5:
          wdt = "West"
      elif winddir < 337.5:
          wdt = "Northwest"
      else:
          wdt = "North"
  
      # ===== get outside temperature =====
      # typical temperature: {'temp_max': 295.15, 'temp_kf': None, 'temp': 292.89, 'temp_min': 290.15}
      # temperature is in Kelvin,
      # Kelvin to Celsius, subtract 273.15
      # Celsius to Fahrenheit, Tf = Tc * 9/5 + 32
      ftc = temperature - 273.15
      tf = int((ftc * 9.0 / 5.0) + 32.5)
  
      # ===== combine status, temperature and humidity into a weather message =====
      msg = 'Weather: {}, {:.1f}F with {}% RH'.format(weather, tf, humidity)
      
      # ===== combine wind direction and wind speed into a weather message =====
      # "Wind from the Northeast at 25mph"
      msg += ', Wind from the {} at {:.1f}mph'.format(wdt, windspeed)
      
      if windgust > 0:
        msg += ', gusting to {}mph'.format(windgust)

      print msg        
      list.append([randomColor(), msg])
      
      dirtyLock.acquire()
      del weatherList[:]
      dirtyFlag = True
      weatherList += list
      dirtyLock.release()
      del list[:]
      
    else:
      print 'Bad error code: {}'.format(r.status_code)
      
                
    # sleep for some number of seconds
    time.sleep(delay)
  # while
          
#==============================================================================
# Get weather forecast for the next 5 days from OpenWeatherMap.org. We only use
# the next day forecast. There are forecasts for every 3 hours for each day.
# 
def getForecast():
  global forecast
  global weatherKey
  global weatherZip
  global forecastList
  global dirtyFlag
    
  list = []
  delay = 900       # update every 15 minutes
  
  print 'Get Forecase'
  
  while True:
    print "Updating forecast information"
    
    try:
      url = 'http://api.openweathermap.org/data/2.5/forecast?zip={}&APPID={}'.format(weatherZip, weatherKey)
      r = requests.get(url)
    except:
      # this occurs when we cannot connect to the OpenWeatherMap service    
      print "Unable to connect to OpenWeatherMap.org, Key or Zipcode may be invalid"

    # parse the forcast data
    if 200 == r.status_code:
      # parse the forecast information
      print '====='
      print r.text
      print '====='
      wlist = r.text.split(',')
      for l in wlist:
        print l
        
#==============================================================================
# find and cleanup any Unicode
def cleanupUnicode(str):
  str = string.replace(str, '\u0026', '&')
  str = string.replace(str, '&#x27;', '\'')
  str = string.replace(str, '&#x39;', '9')
  return str    

#==============================================================================
# Get a headlines from the Internet. Parse out each headline. There may be
# multiple headline URLs. Use a different URL each time this is invoked. Parsing
# is unique to each url.
def getHeadlines():
  global newsUrls
  global newsList
  global dirtyFlag

  headlines = []
  delay = 1800        # 30 minutes
  headlinesIndex = 0
  
  while True:
    url = newsUrls[headlinesIndex]
    headlinesIndex += 1
    if headlinesIndex >= len(newsUrls):
      headlinesIndex = 0
  
    # try to get some headlines
    try:
      print 'Parsing from: {}'.format(url)
      r = requests.get(url)
    except:
      print 'Failed to connect to URL: {}'.format(url)
      
    finally:
      if 200 == r.status_code:
        # a valid page was returned, parse out the headlines
        if url.find('news.google.com') > 0:
          # parse google headlines
          headlines = parseGoogleYahoo(r.text, 'true","')
        elif url.find('www.yahoo.com') > 0:
          # parse yahoo headlines
          headlines = parseGoogleYahoo(r.text, 'alt="')
        elif url.find('hosted2.ap.org') > 0:
          # parse AP headlines
          headlines = parseAP(r.text)
        else:
          # unknow URL
          print 'Unknown URL: {},  unable to parse'.format(url)
          
        if len(headlines) > 0:
          # protect globals
          dirtyLock.acquire()
          del newsList[:]
          dirtyFlag = True
          newsList += headlines
          dirtyLock.release()
          del headlines[:]
      else:
        # bad URL
        print 'Error code: {}'.format(r.status_code)

    # sleep for some number of seconds
    time.sleep(delay)
  # while
  
#==============================================================================
def parseGoogleYahoo(page, key):
  list = []
  print 'Parsing Headlines from Google or Yahoo'
  pos = page.find(key)
  while pos >= 0:
    # found a headline
    pos += len(key)
    pos1 = page.find('"', pos)
    if pos1 > pos:
      # headline is from pos to pos1
      try:
        s = page[pos:pos1]
        list.append([randomColor(), cleanupUnicode(s)])
      except:
        print 'Invalid ascii encoding'
      
    pos = page.find(key, pos1)
  # while

  # add the headlines to the headlines list
  print '===== Headlines ====='
  print 'Found {} headlines'.format(len(list))

  for hl in list:
    print hl[1]
    
  return list        

    
#==============================================================================
def parseAP(page):
  list = []
  key = 'rel="bookmark">'  
  print 'Parsing Headlines from AP'
  
  pos = page.find(key)
  while pos >= 0:
    # found a headline
    pos1 = page.find('</a>', pos)
    if pos1 > pos:
      # headline is from pos to pos1
      list.append([randomColor(), page[pos + len(key):pos1].encode('ascii')])
      
    pos = page.find(key, pos1)
  # while
        
  # add the headlines to the headlines list
  print '===== Headlines ====='
  print 'Found {} headlines'.format(len(list))

  for hl in list:
    print hl[1]

  return list        
  
#==============================================================================
# convert hex-ascii pairs to integers. the order of the bytes is reversed,
# lsb first, msb second.
def convert(lsb, msb, signed):
  msb <<= 8
  x = msb | (lsb & 0x000000FF)
  if signed == SIGNED and x >= 32767:
    x -= 65536
  return x
        
#==============================================================================
# Read the configuration data from the BME280. Configuration data is used to
# convert the raw sensor data to compensated values. This is done once.
# The data is read as a collection of bytes. Bytes are combined into signed or
# unsigned values and stored in Lists.
def getBME280Config():
  global digT1
  global digT2
  global digT3
  global digP1
  global digP2
  global digP3
  global digP4
  global digP5
  global digP6
  global digP7
  global digP8
  global digP9
  global digH1
  global digH2
  global digH3
  global digH4
  global digH5
  global digH6
  global Bme

  raw = bytearray()  
  raw = Bme.read_i2c_block_data(BMEADRS, BME280_DIG_T1_LSB_REG, 6)
  
  digT1 = convert(raw[0], raw[1], UNSIGNED)
  digT2 = convert(raw[2], raw[3], SIGNED)
  digT3 = convert(raw[4], raw[5], SIGNED)
 
#  print 'Temp:' 
#  print raw
#  print str(raw[0]) + ', ' + str(raw[1]) + ' -> ' + str(digT1)
#  print str(raw[2]) + ', ' + str(raw[3]) + ' -> ' + str(digT2)
#  print str(raw[4]) + ', ' + str(raw[5]) + ' -> ' + str(digT3)
  
  raw = Bme.read_i2c_block_data(BMEADRS, BME280_DIG_P1_LSB_REG, 18)
  digP1 = convert(raw[0], raw[1], UNSIGNED)
  digP2 = convert(raw[2], raw[3], SIGNED)
  digP3 = convert(raw[4], raw[5], SIGNED)
  digP4 = convert(raw[6], raw[7], SIGNED)
  digP5 = convert(raw[8], raw[9], SIGNED)
  digP6 = convert(raw[10], raw[11], SIGNED)
  digP7 = convert(raw[12], raw[13], SIGNED)
  digP8 = convert(raw[14], raw[15], SIGNED)
  digP9 = convert(raw[16], raw[17], SIGNED)

#  print 'Pressure:'
#  print raw
#  print str(raw[0]) + ', ' + str(raw[1]) + ' -> ' + str(digP1)
  
#  print 'Humidity:'
  digH1 = Bme.read_byte_data(BMEADRS, BME280_DIG_H1_REG) & 0x000000FF

#  print str(raw[0]) + ' -> ' + str(digH1)
  
  raw = Bme.read_i2c_block_data(BMEADRS, BME280_DIG_H2_LSB_REG, 7)
  digH2 = convert(raw[0], raw[1], SIGNED)
  digH3 = raw[2] & 0x000000FF
  
  digH4 = raw[3] << 4
  digH4 = digH4 | (raw[4] & 0x0F)
  
  digH5 = raw[5] << 4
  digH5 = digH5 | raw[4] >> 4
  
  digH6 = raw[6]

#  print raw
#  print str(raw[0]) + ', ' + str(raw[1]) + ' -> ' + str(digH2)
#  print str(raw[2]) + ' -> ' + str(digH3)
#  print str(raw[3]) + ', ' + str(raw[4]) + ' -> ' + str(digH4)
#  print str(raw[4]) + ', ' + str(raw[5]) + ' -> ' + str(digH5)
#  print str(raw[6]) + ' -> ' + str(digH6)

#==============================================================================
def getBME280():
  global sensorList
  global lastPressure
  global humidity
  global temperature
  global pressure
  global digT1
  global digT2
  global digT3
  global digP1
  global digP2
  global digP3
  global digP4
  global digP5
  global digP6
  global digP7
  global digP8
  global digP9
  global digH1
  global digH2
  global digH3
  global digH4
  global digH5
  global digH6
  global Bme
  
#  global Temperature
#  global Humidity
  global Barometer
  

  # verify BMW280 is present by reading chip ID
  try:
    reply = Bme.read_byte_data(BMEADRS, BME280_CHIP_ID_REG)
#    print 'BME280: 0x' + hex(reply)
  except:
    print 'BME280 not found, check wiring'
    return
      
  # initialize BME280
  Bme.write_byte_data(BMEADRS, BME280_CTRL_MEAS_REG, 0x00)
  Bme.write_byte_data(BMEADRS, BME280_CONFIG_REG, 0xA0)
  Bme.write_byte_data(BMEADRS, BME280_CTRL_HUMIDITY_REG, 0x01)
  Bme.write_byte_data(BMEADRS, BME280_CTRL_MEAS_REG, 0x27)
  
  # read the compensation data, combine bytes and store it
  getBME280Config()
    
  list = []
  raw = bytearray()  
  
  # ten minutes between readings
  delay = 600
  while True:
    # read raw data from the sensor array
    raw = Bme.read_i2c_block_data(BMEADRS, BME280_PRESSURE_MSB_REG, 8)

    # convert raw data bytes to 32 bit variables 
    p =  raw[0]
    p = p << 8 | raw[1]
    p = p << 4 | raw[2] >> 4
  
    t =  raw[3]
    t = t << 8 | raw[4]
    t = t << 4 | raw[5] >> 4
    
    h = raw[6]
    h = h << 8 | raw[7]
    
#    print str(raw[0]) + ', ' + str(raw[1]), ', ' + str(raw[2]) + ' -> ', str(p)
#    print str(raw[3]) + ', ' + str(raw[4]), ', ' + str(raw[5]) + ' -> ', str(t)
#    print str(raw[6]) + ', ' + str(raw[7]), ' -> ', str(h)

    # compensate and convert temperature to C
    # my python coding of the formulas from the user guide
    v1 = (t / 16384.0 - digT1 / 1024.0) * digT2
    v2 = (t / 131072.0 - digT1 / 8192.0) * (t / 131072.0 - digT1 / 8192.0) * digT3
  
    tfine = int(v1 + v2)
    
    # convert temperature to degrees Farhenheit
    if (temperature):
      tc = round((v1 + v2) / 5120.0, 1)
      tf = round((tc * 9 / 5) + 32.05, 1)
      # convert to text
      tmsg = ' {0:0.1f}F'.format(tf)

      # for Celcius temperature replace the three lines above with
      # tc = round((v1 + v2) / 5120.0, 1)
      # tmsg = ' {0:0.1f}C'.format(tc)

      
    # compensate and convert humidity to a percentage
    if (humidity):
      # my python coding of the formulas from the user guide
      fh = tfine - 76800.0
      if fh > 0.0:
        fh = (h - (digH4 * 64.0 + digH5 / 16384.0 * fh)) * (digH2 / 65536.0 * (1.0 + digH6 / 67108864.0 * fh * (1.0 + digH3 / 67108864.0 * fh)))
    
        fh *= (1.0 - digH1 * fh / 524288.0)
    
        if fh > 100.0:
          fh = 100.0
        elif fh < 0.0:
          fh = 0.0
      else:
        fh = 0.0
        
      hmsg = ' {0:0.1f}% RH'.format(fh)

    # compensate and convert pressure to inches of Hg
    if (pressure):
      # my python coding of the formulas from the user guide
      # 1KPa = 0.29531inHg
      v1 = (tfine / 2.0) - 64000.0
      v2 = (((v1 / 4.0) * (v1 / 4.0)) / 2048) * digP6
      v2 += ((v1 * digP5) * 2.0)
      v2 = (v2 / 4.0) + (digP4 * 65536.0)
      v1 = (((digP3 * (((v1 / 4.0) * (v1 / 4.0)) / 8192)) / 8) + ((digP2 * v1) / 2.0)) / 262144
      v1 = ((32768 + v1) * digP1) / 32768
  
      # check for possible divison by zero
      if v1 != 0:
        fp = ((1048576 - p) - (v2 / 4096)) * 3125
        if fp < 0x80000000:
          fp = (fp * 2.0) / v1
        else:
          fp = (fp / v1) * 2
    
        v1 = (digP9 * (((fp / 8.0) * (fp / 8.0)) / 8192.0)) / 4096
        v2 = ((fp / 4.0) * digP8) / 8192.0
        fp += ((v1 + v2 + digP7) / 16.0)
    
      else:
        # something went wrong with the pressure calculation or we just got
        # spaced !!!
        fp = 0.0

      # 1 KPa = 0.29531 inHg (inches of mercury)
      # fair weather -> 1022mb or greater
      # foul weathre -> 988mb or less
    
      # pressure is in hPa or millibars
      fp /= 100.0
      lastPressure = Barometer
      Barometer = fp
  
      # convert to hectoPascals (hPa) or millibars
      pmsg = ' {0:0.1f} millibars'.format(fp)
      if (int(lastPressure) < int(fp)):
        pmsg += ' and rising'
      elif (int(lastPressure) > int(fp)):
        pmsg += ' and falling'
      
      msg = 'Environment:'
      if (temperature):
        msg += tmsg

      if (humidity):
        if (len(msg) > 13):
          msg += ','

        msg += hmsg

      if (pressure):
        if (len(msg) > 13):
          msg += ','
          
        msg += pmsg
      
      list.append([randomColor(), msg])

    if len(list) > 0:
      # protect globals
      dirtyLock.acquire()
      del sensorList[:]
      dirtyFlag = True
      sensorList += list
      dirtyLock.release()
      del list[:]

    # sleep for some number of seconds
    time.sleep(delay)
  # while
    
#==============================================================================
# make a new topList.
def newTopList(): 
  global dirtyLock
  global topList
  
  # all entries have been sent, re-build the topList
  # protect the global resources
  dirtyLock.acquire()
  del topList[:]

  # add time and date messages to the topList
  topList.append([randomColor(), timeMessage()])
  topList.append([randomColor(), dateMessage()])

  dirtyLock.release()
       

#==============================================================================
# make a new bottomList from the feature lists. weather may be added multiple
# times if headlines are enabled.
def newBottomList(): 
  global dirtyFlag
  global dirtyLock
  global newsEnabled
  global sensorList
  global weatherList
  global bottomList
  global jokeList
  global newsList
  
  # all entries have been sent, re-build the bottomList
  if dirtyFlag:
    print "Making New Bottom List"

    # protect the global resources
    dirtyLock.acquire()
    del bottomList[:]
    dirtyFlag  = False
    bottomList += dailyList + quoteList + sensorList + jokeList + weatherList + newsList
    if newsEnabled and len(newsList) > 10:
      bottomList += weatherList

    dirtyLock.release()
       
#==============================================================================
# Check for the holidays that do not occur on the same day every year
# thisday -> day of the month as a string
# day     -> which occurace of the weekday; First Monday, Third Sunday...
# weekday -> dow as a string, same as flags from xml file
def check4Holiday(thisDay, day, flags):
  # assume no match occurs
  result = False
  dayasnumber = int(thisDay)
  
  if day == "First":
    # First occurance
    result = dayasnumber <= 7
  elif day == "Second":
    # Second occurance
    result = dayasnumber > 7 and dayasnumber <= 14
  elif day == "Third":
    # Third occurance
    result = dayasnumber > 14 and dayasnumber <= 21
  elif day == "Fourth":
    # Fourth occurance
    result = dayasnumber > 21 and dayasnumber <= 28
  elif day == "Last":
    # Last occurance only happens in May, 31 days
    result = dayasnumber > 24
  elif day == "Easter":
    # First Sunday after the 21st
    result = dayasnumber >= 21 and dayasnumber < 28
  elif day == "PalmSunday":
    # Week before Easter
    result = dayasnumber >= 14 and dayasnumber < 21
  elif day == "GoodFriday":
    # Friday before Easter
    result = dayasnumber >= 19 and dayasnumber < 26

  return result

#==============================================================================
# load the daily list with messages from the xml file. only messages with a
# matching date are added
def loadFromXml(filename, thisMonth, thisDay, weekday):
  # open & read the xml file into a document
  global dailyList

  if os.path.isfile(filename):
    try:
      doc = minidom.parse(filename)
      items = doc.getElementsByTagName("item")

      # add all entries that have a matching month and day
      for item in items:
        month = item.getElementsByTagName("month")[0].firstChild.data
        day   = item.getElementsByTagName("day")[0].firstChild.data
        flags = item.getElementsByTagName("flags")[0].firstChild.data
        linenum = str(item.getElementsByTagName("line")[0].firstChild.data)
        bc =      str(item.getElementsByTagName("backgnd")[0].firstChild.data)
        fc =      str(item.getElementsByTagName("foregnd")[0].firstChild.data)
        txt =     str(item.getElementsByTagName("text")[0].firstChild.data)

        # Holidays and Birthdays must match the current month and day
        if month == thisMonth:
          if day == thisDay or day == '0' or day == '00':
            dailyList.append([randomColor(), txt])
          # these are holidays that fall on a selected weekday, not a date
          elif flags == weekday and check4Holiday(thisDay, day, flags):
            dailyList.append([randomColor(), txt])

    except xml.dom.DOMException:
      print "DOM faliure reading from " + filename
  else:
    print 'File not found: ' + filename
                  
#==============================================================================
# this class handles the driving of the RGB matrix. Each line ahs a list
# of messages to scroll. Each list entry is a list that contains the color to use
# and the text to display.
class RunText(SampleBase):
  def __init__(self, *args, **kwargs):
    super(RunText, self).__init__(*args, **kwargs)
    self.parser.add_argument("-c 2","-t", "--text", help="The text to scroll on the RGB LED panel", default="Big J Wins Again!")

  def run(self):
    global topList
    global topIndex
    global bottomList
    global bottomIndex
        
    offscreen_canvas = self.matrix.CreateFrameCanvas()
    font = graphics.Font()
    # change the 7x13.bdf filename to use a different font.
    font.LoadFont("fonts/7x13.bdf")

    # default colors    
    topColor = graphics.Color(255, 255, 0)
    bottomColor = graphics.Color(0, 0, 255)
    
    pos1 = offscreen_canvas.width
    pos2 = offscreen_canvas.width
    
    my_text = self.args.text

    while True:
      offscreen_canvas.Clear()
      
      if (len(topList) > 0):
        topColor = topList[topIndex][0]
        msg = topList[topIndex][1]
      else:
        msg = 'Please Wait for Raspberry Pi to boot'
        
      # determine the pixel length of the message
      msglen = graphics.DrawText(offscreen_canvas, font, pos1, Row1, topColor, msg)
      pos1 -= 1
      # check for message scroll complete
      if (pos1 + msglen < 0):
        # scroll complete, change message & start scrolling
        pos1 = offscreen_canvas.width
        
        # iterate through topList one message at a time
        topIndex += 1
        if (len(topList) <= topIndex):
          # end of the list, start over
          topIndex = 0
          # make new topList
          newTopList()

      # scroll bottom line
      if (len(bottomList) > 0):
        bottomColor = bottomList[bottomIndex][0]
        msg = bottomList[bottomIndex][1]
      else:
        msg = 'Please Wait while I gather information from the Internet'
        
      # determine the pixel length of the message
      msglen = graphics.DrawText(offscreen_canvas, font, pos2, Row2, bottomColor, msg)
      pos2 -= 1
      # check for message scroll complete
      if (pos2 + msglen < 0):
        # scroll complete, change message & start scrolling
        pos2 = offscreen_canvas.width
        
        # iterate through bottomList one message at a time
        bottomIndex += 1
        if (len(bottomList) <= bottomIndex):
          # end of the list, start over
          bottomIndex = 0
          # make new bottomList
          newBottomList()
          
#        print bottomList[bottomIndex][1]

#      time.sleep(0.05)
      time.sleep(0.025)
      offscreen_canvas = self.matrix.SwapOnVSync(offscreen_canvas)

#==============================================================================
def setup(): 

  global quoteEnabled
  global quoteUrl
  global jokesEnabled
  global jokesUrls
  global jokesDelay
  global weatherEnabled
  global weatherKey
  global weatherZip
  global newsEnabled
  global newsUrls
  
#  global log
  
  print "NTP: " + getNTPTime()
  
  # initialize the randon number generator
  random.seed()
  
  # dailyList does not use a thread for updating
       
  # read the options file     
  readOptions('options.ini')
  
  # add time and date messages to the topList
  newTopList()
    
  # create a thread to update the Quote-of-the-day once an hour
  if quoteEnabled and len(quoteUrl) > 0:
    try:
      thread.start_new_thread(getQuoteOfTheDay, ())
    except:
      print 'Error: unable to create Quotes thread'

  # create a thread to update jokes every 20 minutes
  if jokesEnabled and len(jokesUrls) > 0:
    if 0 == jokesDelay:
      jokesDelay = 1200
      
    try:
      thread.start_new_thread(getAJoke, ())
    except:
      print 'Error: unable to create Jokes thread'

  # create a thread to update the weather info every ten minutes
  if weatherEnabled and len(weatherKey) > 0 and len(weatherZip) > 0:
    try:
      print 'Creating Weather thread'
      thread.start_new_thread(getWeather, ())
    except:
      print 'Error: unable to create Weather thread'
  else:
    print 'Weather thread failed'
    
  # create a thread to update the BME280 sensor data every ten minutes
  try:
    thread.start_new_thread(getBME280, ())
  except:
    print 'Error: unable to createBME280 thread'

  # create a thread to update news headlines once an hour
  if newsEnabled and len(newsUrls) > 0:
    try:
      thread.start_new_thread(getHeadlines, ())
    except:
      print 'Error: unable to create Headlines thread'

  # add messages to the bottomList
  newBottomList()

#==============================================================================
# Main function

setup()
if __name__ == "__main__":
  run_text = RunText()
  if (not run_text.process()):
    run_text.print_help()
