> set style data histograms
> 
> set terminal svg size 2048,2048 enhanced
> set output "timings.svg"
> 
> set boxwidth
> set style fill solid 1.0
> set ydata time
> set timefmt "%m:%s"
> unset xtics
> 
> plot "doc/86timings.csv" using 2:xtic(1) title "Coq 8.6" lt rgb "#406090", \
>      "doc/87timings.csv" using 2:xtic(1) title "Coq 8.7" lt rgb "#40FF00"
