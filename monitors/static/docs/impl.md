# Implmentation

## Dynamic Programming for MLTL Verification

### Abstract Syntax Tree
We use the dynamic programming proposed in [7] to compute the satisfaction of the MLTL. The first step is to break the MLTL formula into subformulas. We let the user describe their desired MLTL specification in a high-level (or assembly like) language. Then a compiler converts the formula into an Abstract Syntax Tree (AST). The AST explicitly exposes the logical connection between each observer node. We can then verify MLTL satisfaction of an input trace by checking the tree from leaf to root. For example, $\square_{[0,2]}(!a0)$ can be convert into the following execution sequence '$s0\rightarrow s1\rightarrow s2$' in our customized assembly language format:
\begin{equation*}
\begin{split}
 Line\, 0:\qquad & s0 \leftarrow load\: (a0,time)\\
 Line\, 1:\qquad & s1 \leftarrow \neg\: s0\\
 Line\, 2:\qquad & s2 \leftarrow \square_{[0,2]}\: s1
\end{split}
\end{equation*}

Where each subformula is an observer node (e.g., s0, s1, s2). The output from each node is a tuple containing a verdict and its corresponding timestamp (RTC) $\tau$. The last line $s2$ is the final result.

### Abstrct Syntax Tree (AST) Optimization
For some \mltl formulas, certain sub-expressions occur more than once. An example formula is $G[2,4]a0\&!a0$. The compiler will generate an extra line of assembly code to load atomic $a0$ twice. Thus, it takes two separate queues for loading $a0$. There are two drawbacks of this: 1) memory resource wasting: extra queue is taken; 2) computation speed decrease: more assembly instructions to execute. Here we can do the following operations, as mentioned in~\cite{jakvsic2015signal}, to remove duplicate branches when synthesizing an \mltl formula into an AST. However, to support such optimization, the traditional hardware memory queue should be redesigned to support multiple readers. That is why we propose using an SCQ. The detailed optimization steps are described below.

\begin{figure}
\centering
\includegraphics[width=0.65\textwidth]{fig/opt_ast.pdf}
\caption{\label{fig:ast}Example of optimizing an AST from A to B. Both node 3 and 4 share the same key string, so we cut edge (node 1 $\rightarrow$ node 3) and connect edge (node 1 $\rightarrow$ node 4). The connections of SCQs and nodes are also shown in the figure.}
\end{figure}

- Do an inorder traverse to the unoptimized AST. Map each node to a string which represents its traverse order. We add '(' and ')' to each recursive traverse thus each string is uniquely represented in the branch structure.
- Map each string to its root node. Whenever we traverse from a new node, we check whether the string already exists. If two strings are identical, we can reconnect the edge as shown in Figure.~\ref{fig:ast}.
- Search from the root node to valid nodes in the tree. Then do a topological sort from the root node to arrange the node operator execution sequence.

### Shared Connection Queue (SCQ)
We employ what we call SCQs to store subformula results. An SCQ is a circular buffer (CB) with one write pointer and one or more read pointers. A similar data structure is proposed in \cite{4812537} for processing network streams. Figure.~\ref{fig:scq} shows how SCQs are embedded in an \mltl abstract syntax tree. There are two reasons we use the SCQ: 1) Each subformula may produce more than one tuple; 2) more than one parent nodes may read data from a given subformula.

The SCQ follows a writing rule called \textbf{Aggregation}, by which sequential input's timestamp will be overwritten by the later timestamp value if they have the same verdict. For example, if the data content is (true, 10), (false, 15), it means that during timestamp interval [11,15], the verdicts are all false. If the next input is (false, 16), the data content becomes (true, 10), (false, 16). The SCQ write and read algorithms are shown in Algorithm. \ref{ag:wr}, \ref{ag:rd}.

\begin{figure}
\centering
\includegraphics[width=0.6\textwidth]{fig/scq_cb.pdf}
\caption{\label{fig:scq}Detailed implementation of SCQs between observer nodes. The component in the dashed box is the abstract representation of connected observer nodes.}
\end{figure}

#### SCQ Algorithms

\begin{algorithm}
\SetAlgoLined
\SetKwInOut{Input}{input}
\Input{$new\_data$}
 \If{$new\_data$ is not Empty}{
 \If{$SCQ[SCQ.wr\_ptr].v == new\_data.v$}{$SCQ.wr\_ptr --$\;}
  $ SCQ[SCQ.wr\_ptr]\leftarrow new\_data$\;
  $SCQ.wr\_ptr ++$\;
  }
 \caption{\label{ag:wr}Function: write()}
\end{algorithm}

#### Read
The write operation algorithm is shown in Algorithm.~\ref{ag:rd}.
\begin{algorithm}
\SetAlgoLined
\SetKwInOut{Input}{input}
\SetKwInOut{Output}{output}
\Input{$\&rd\_ptr$, $\tau_e$}
\Output{$Empty$ or $read\_data$}
  \If{read}{
  \If{$*rd\_ptr==SCQ.wr\_ptr$}{
    \KwRet{Empty}\;
  }
    $read\_data\leftarrow SCQ[*rd\_ptr]$\;
    \While{$read\_data.\tau <\tau_e$}{
      $rd\_ptr++$\;
      \If{$*rd\_ptr==SCQ.wr\_ptr$}{
        \KwRet{Empty}\;
      }
      $read\_data\leftarrow SCQ[*rd\_ptr]$\;
    }
   \KwRet{$read\_data$}\;
  }
 \caption{\label{ag:rd}Function: read()}
\end{algorithm}

#### SCQ Utilization
Most of the observer processor core's memory is used by the input SCQs for binary operators: $\wedge$, $\vee$ and $\mathcal{U}$. Due to the timestamp mismatch between the two inputs, the input with a more recent timestamp has to be stalled in the SCQ. Here we define the best-case-delay (\textbf{bcd}) and worst-case-delay (\textbf{wcd}) to analyse the timestamp mismatch. The \textbf{bcd} is the earliest or best delay output time relative to the current real-time clock (RTC) and \textbf{wcd} in the latest/worst delay. The delay is produced by temporal operators like $\square$, $\Diamond$ and $\mathcal{U}$. Each temporal operator adds the $lb$ to \textbf{bcd} and $ub$ to \textbf{wcd}. The maximum size of a given SCQ can be determined by taking its \textbf{bcd} and minus the \textbf{wcd} of the other input.\par

To allocate the SCQ size for all operator nodes, we first recursively decide the \textbf{bcd} and \textbf{wcd} of each operator from the bottom to the root node. Algorithm.~\ref{ag:sq} then uses this information to compute the queue size for each node.\par

\begin{algorithm}
    \SetAlgoLined
    \SetKwInput{KwData}{Var}
    \SetKwInOut{KwInit}{Init}
    \SetKwProg{Fn}{Function}{}{end}
    \SetKwComment{comment}{$\LHD$}{}
    % \SetKwInOut{Input}{input}
    % \SetKwInOut{Output}{output}
    % \KwData{$\tau_e$}\
    % \Input{ss}\
    
    \KwInit{assign all nodes' output SCQ size $\leftarrow$ 1}
    compute \textbf{bcd} and \textbf{wcd} of each node from bottom up\;
    \For{every node $\mathcal{N}$}{
      assign output SCQ size of $\mathcal{N}$\;
    }
    
    
    \Fn{assign output SCQ size (node $\mathcal{N}$)}{
    set $\{wcd\} \leftarrow \varnothing$ \;
    \For{$\mathcal{N}$'s every binary parent node $\mathcal{N}.bp$}{
      add \textbf{wcd} of the other child node of $\mathcal{N}.bp$ to $\{wcd\}$\;
    }
    find the maximum \textbf{wcd} of $\{wcd\}$ set: $max(wcd)$\;
    get output SCQ size of $\mathcal{N} \leftarrow max(wcd)-\mathcal{N}.bcd+1$\;
    }
     \caption{\label{ag:sq}Determine the size of SCQ}
\end{algorithm}


Detailed implementation of Algorithm. \ref{ag:sq}.
\begin{algorithm}
\SetAlgoLined
\SetKwInput{KwData}{Var}
\SetKwProg{KwInit}{Init}{}{end}
\SetKwProg{Fn}{Function}{}{end}
\SetKwComment{comment}{$\LHD$}{}
% \SetKwInOut{Input}{input}
% \SetKwInOut{Output}{output}
% \KwData{$\tau_e$}\
% \Input{ss}\

\KwInit{}{
\For{all node n in observer node set}{
  Init $n.SCQ\_size \leftarrow 1$
  \If{$n.operator = \mathcal{L}$}{
    $n.bcd, n.wcd \leftarrow 0, 0$\;
    put node $n$ in $visited[]$\;
  }
}
}
$Assign\_Queue\_Size($root node$)$\;
\Fn{Assign\_Queue\_Size(node n)}{
  \If{n.operator == $\wedge | \vee | \mathcal{U}$}{
    $\mu \leftarrow n.left\_child$\;
    $\nu \leftarrow n.right\_child$\;
    \If{$\mu$ \textbf{not} in $visited[]$}{
      $Assign\_Queue\_Size(\mu)$\;
    }
    \If{$\nu$ \textbf{not} in $visited[]$}{
      $Assign\_Queue\_Size(\nu)$\;
    }
    \uIf{n.operator == $\wedge | \vee$}{
      $n.bcd \leftarrow min(\mu.bcd, \nu.bcd)$\;
      $n.wcd \leftarrow max(\mu.wcd, \nu.wcd)$\;
    }\ElseIf{n.operator == $\mathcal{U}$}{
      $n.bcd \leftarrow min(\mu.bcd, \nu.bcd) + min(n.J)$\;
      $n.wcd \leftarrow max(\mu.wcd, \nu.wcd) + max(n.J)$\;
    }
       $\mu.SCQ\_size\leftarrow max(\mu.SCQ\_size,\nu.wcd-\mu.bcd+1)$\;
       $\nu.SCQ\_size\leftarrow max(\nu.SCQ\_size,\mu.wcd-\nu.bcd+1)$\;
  }
  \If{n.operator == $\square | \Diamond | \neg$}{
    $\mu \leftarrow n.child$\;
    \If{$\mu$ \textbf{not} in $visited[]$}{
      $Assign\_Queue\_Size(\mu)$\;
    }
    \uIf{n.operator == $\square | \Diamond$}{
      $n.bcd \leftarrow \mu.bcd + min(n.J)$\;
      $n.wcd \leftarrow \mu.wcd + max(n.J)$\;
    }\ElseIf{n.operator == $\neg$}{
      $n.bcd \leftarrow \mu.bcd$\;
      $n.wcd \leftarrow \mu.wcd$\;
    }
  }
  put node $n$ in $visited[]$\;
}
 \caption{\label{ag:sq_d}Determine the size of SCQ}
\end{algorithm}


