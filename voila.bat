@echo off
SetLocal EnableDelayedExpansion

java -Xss128m -cp target\scala-2.13\voila.jar viper.voila.VoilaRunner %*
