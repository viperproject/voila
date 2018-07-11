# Original taken from
#   https://github.com/quornian/config/blob/master/bash/exec-hook.bash



# Set up a cool demo prompt.
# Note the trailing change to high-intensity bold white, which will
# be "closed" by preexec.
export PS1="\[\e[38;5;63m\][\u@demo|\A]\[\e[m\]\n$ \[\e[1;97m\]"



# Set up a convenient alias for verifying a Voila file

__voila() {
  $VOILA_CMD -i "$(realpath $1)"
}

alias voila='__voila'



# Install scripts that are executed before and after each command invoked by the shell

preexec() { 
  echo -ne "\e[0m";  # Return to normal mode
}

postexec() {
  # Transforms $PRE_COMMAND to lower-case to achieve case-insensitive string comparison
  # https://stackoverflow.com/questions/1728683
  [ "${PRE_COMMAND,,}" = "clear" ] && return # Don't do anything after clear
  
  echo ""; # Have an empty line after the executed command terminated, i.e. before
           # the prompt is show again
}

preexec_invoke_exec () {
  [ -n "$COMP_LINE" ] && return  # Completing -> do nothing
  [ "$BASH_COMMAND" = "$PROMPT_COMMAND" ] && return # Setting prompt -> do nothing
  PRE_COMMAND=$BASH_COMMAND # Store the command that is about to be executed
  preexec "$(history 1 | sed -e "s/^[ ]*[0-9]*[ ]*//g")";
}

trap 'preexec_invoke_exec' DEBUG # Execute preexec_invoke_exec before each command
PROMPT_COMMAND='postexec' # Execute postexec afterwards
