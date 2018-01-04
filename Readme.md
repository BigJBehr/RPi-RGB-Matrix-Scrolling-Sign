# Raspberry Pi RGB LED Matrix Scrolling Sign
This project is for a Raspberry Pi based RGB LED Matrix scrolling sign. A python script running on the Raspberry Pi uses WiFi and your internet connection to collect data from various web sites. The collected data is parsed, formatted and display on the RGB Matrix as scrolling text messages. The sign scrolls; time, date, quote-of-the-day, jokes, local weather, environment data, headlines, birthday greetings and holiday messages. The birthday and holiday greetings are user definable by editing a pair of XML files. Complete instructions on how to build one of these is available on the Instructables web site here; https://www.instructables.com/id/Raspberry-Pi-Scrolling-Sign/.

This is a list of the files found here. All of these files should be in the same directory on your Raspberry Pi.
    RGB-32x64.py    - python script that runs the scrolling display
    options.ini     - configuration file that is used to enable/disable features
    birthdays.xml   - file of birthday messages and dates
    holidays.xml    - file of holiday messages and dates
    samplebase.py   - python script from the Henner Zeller RGB matrix library
    fonts           - fonts directory from the Henner Zeller RGB matrix drive library
    Eagle           - this folder contains the Eagle files required to make your own boards

The Henner Zeller RGB matrix library should also be in this directory. You can get the library here; https://github.com/hzeller/rpi-rgb-led-matrix

## The Eagle folder has a zip file that has what is needed to send to a board manufacturer to make boards for you. It also has the Eagle schematic and board layout files and a PDF of the schematic.

Enjoy
