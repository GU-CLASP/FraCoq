/lin .* = .*;/{
    sub(/lin/,"Definition")
    sub(/=/,":=")
    sub(/;/,".")
    if (!(match($2,/._q$/))) # remove the questions
        if (!match($0,/variants/)) # apparently broken things
            print;
}
