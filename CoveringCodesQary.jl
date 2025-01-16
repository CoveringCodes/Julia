using JuMP, SDPAFamily, LinearAlgebra, Combinatorics
setprecision(512)

function DetermineOrbitNumbersQary(n)
    orbitNumbers= Dict();
    orbitNumber=0;
    ## instead of storing orbit representatives as triples [i,j,t,p] 
    ## in my code they are stored as quintuples [i1,i2,i3,i4,i5], where 
    ##
    # i1 = n-(i-t)-(j-t)-p-(t-p) is the number of positions x000
    # i2 = j-t                   is the number of positions x001  
    # i3 = i-t                   is the number of positions x010    
    # i4 = p;                    is the number of positions x011
    # i5 = t-p;                  is the number of positions x012
    
    function numberOrbit(i,j,t,p)
        for tprime=0:n, iprime=0:n, jprime=0:n, pprime=0:tprime  
            if n>=n-iprime-jprime+tprime>=0 && n>=jprime-tprime >=0 && n>= iprime-tprime >= 0  &&  (isequal(sort([i,j,i+j-t-p]), sort([iprime,jprime,iprime+jprime-tprime-pprime])) && t-p == tprime-pprime )
                orbitNumbers[[n-iprime-jprime+tprime, jprime-tprime, iprime-tprime, pprime, tprime-pprime]] =orbitNumber 
            end
        end
    end

    #first number the orbits x_{i,0}^{0,0} where i=0,...,n 
    for i=0:n 
        if !haskey(orbitNumbers, [n-i, 0, i, 0, 0])
            orbitNumber+=1
            numberOrbit(i,0,0,0)
        end
    end
    for t=0:n, i=0:n, j=0:n, p = 0 : t  
        if n>=n-i-j+t>=0 && n>=j-t >=0 && n>= i-t >= 0 && !haskey(orbitNumbers, [n-i-j+t, j-t, i-t, p, t-p])
            orbitNumber+=1
            numberOrbit(i,j,t,p)
        end
    end
    return orbitNumbers, orbitNumber
end

function DetermineBlockIndicesQ(n,k,a) 
    IndexSet=[]
    #rowindex: number of ones in first row of tableau 1
    for i=k:n+a-k
    #rowindex: number of ones in first row of tableau 2 
        push!(IndexSet,i);
    end
    return IndexSet, size(IndexSet,1)
end

function gammaprime(n, i2,i3,i4,i5,q=3)
    return big(q-1)^(i2+i3+i4+i5)*big(q-2)^(i5)*multinomial(big(i2),big(i3),big(i4),big(i5),big(n-i2-i3-i4-i5))
end

function beta(m,t,i,j,k)
    return sum([(-1)^(t-u)*binomial(big(u),t)*binomial(big(m-2*k),m-k-u)*binomial(big(m-k-u),i-u)*binomial(big(m-k-u),j-u) for u=0:m])
end

function alpha(n,i,j,t,p,a,k,q=3)
    start= beta(n-a,t-a,i-a,j-a,k-a)*big(q-1)^(i+j-t)
    start2=0;
    for g=0:p 
        if  t-a >=p-g && a >=0
            start2+=(-1)^(a-g)*binomial(big(a),g)*binomial(big(t-a),p-g)*big((q-2))^(t-a-p+g)
        else 
            start2+=0
        end
    end
    return start*start2
end
   
#Given words x,y with d(x,y)=(i,j,t,p), calculate for each j',t',p' the number
#Coef[j',t',p']:=sum_d lambda_d*
#|words z: d(y,z)=d, d(x,z)=(i,j',t',p')|.
#this is needed for inequality row x around word y.
##lambda is a vector of size n+1. lambda[dist+1] corresponds with lambda_dist from the paper. 
function MakeDistrQary(n,i,j,t,p,lambda,q=3)
	ti=i-t;
	tj=j-t;
    tp = t-p;
    rest=n+t-i-j
	coef=Dict();

    #add values
	for a1=0:ti, a2=0:ti-a1, b1=0:tj, b2=0:tj-b1, c1=0:p, c2=0:p-c1, d1=0:tp, d2=0:tp-d1, d3=0:tp-d1-d2, e=0:rest
        j2=a1+a2+b1+b2+c1+c2+d1+d2+d3+e;
        t2=a1+a2+c1+c2+d1+d2+d3;
        p2=a1+c1+d1
        dist=a1+a2+e+j-b1-c1-d2;	
        if haskey(coef,(j2,t2,p2))
            coef[j2,t2,p2]+=lambda[dist+1]*multinomial(big(ti-a1-a2),a1,a2)*multinomial(big(tj-b1-b2),b1,b2)*multinomial(big(p-c1-c2),c1,c2)*multinomial(big(tp-d1-d2-d3),d1,d2,d3)*binomial(big(rest),e)*big(q-1)^e*big(q-2)^(a2+b2+c2)*big(q-3)^d3
        else
            coef[j2,t2,p2]=lambda[dist+1]*multinomial(big(ti-a1-a2),a1,a2)*multinomial(big(tj-b1-b2),b1,b2)*multinomial(big(p-c1-c2),c1,c2)*multinomial(big(tp-d1-d2-d3),d1,d2,d3)*binomial(big(rest),e)*big(q-1)^e*big(q-2)^(a2+b2+c2)*big(q-3)^d3
        end
    end         
	return coef;
end

function CovQary(n,radius, q=3)
    orbitNumbers, nVars=DetermineOrbitNumbersQary(n);

    opt = SDPAFamily.Optimizer(variant= :sdpa_gmp,verbose=SDPAFamily.VERBOSE,
    presolve = true, silent=false,
    params = (  lambdaStar=1e12, epsilonStar = 1e-30, betaStar=0.2, betaBar=0.4, gammaStar=0.5,# constraint tolerance
                epsilonDash = 1e-30, precision=512, upperBound=1e20, lowerBound=-1e20 
    ))
    model =GenericModel{BigFloat}()#Model() 

    set_optimizer(model, () -> opt)

    @variable(model, y[1:nVars])

    for i=1:nVars
        @constraint(model, y[i]>=0)
    end

    objectivepoly = 0; 
    for i2=0:n,i3=0:n-i2,i4=0:n-i2-i3,i5=0:n-i2-i3-i4
        objectivepoly += gammaprime(n,i2,i3,i4,i5,q)*y[orbitNumbers[[n-i2-i3-i4-i5,i2,i3,i4,i5]]]
    end
    @objective(model,Min,objectivepoly)
  
    println("starting block generation of semidefinite constraints...")
    #Generate block-diag of matrix corresponding to 3-tuples
    for a=0:n, k=a:n 
        if k <= n+k-a 
            #Create a new block in the block diagonalization
            IndexSet, blockSize = DetermineBlockIndicesQ(n,k,a)
            if blockSize >0 
                X =zeros(GenericAffExpr{BigFloat, GenericVariableRef{BigFloat}},blockSize,blockSize) #zeros(AffExpr,blockSize,blockSize) #
                for rowIndex = 1:blockSize
                    for columnIndex = 1:blockSize 
                        i = IndexSet[rowIndex]; 
                        j = IndexSet[columnIndex];
                        for t=0:n, p=0:t
                            i4= p; i5=t-p; 
                            i3 = i-t; 
                            i2 = j-t; 
                            i1 = n-(i-t)-(j-t)-p-(t-p)
                            #t=i4+i5;p=i4; i== i3+i4+i5 && j==i2+i4+i5 
                            if i1>=0 && i2 >=0 && i3 >=0 && i4 >=0 && i5 >=0
                                X[rowIndex,columnIndex]+=y[orbitNumbers[[i1,i2,i3,i4,i5]]]*alpha(n,i,j,t,p,a,k,q)
                            end
                        end
                    end
                end
                @constraint(model, X >=0, PSDCone())
            end
        end
    end

    #generate block-diag of semidefinite constraint matrix corresponding to 2tuples-3tuples 
    for a=0:n, k=a:n 
        if k <=n+k-a 
            #Create a new block in the block diagonalization
            IndexSet, blockSize = DetermineBlockIndicesQ(n,k,a)
            if blockSize >0
                addValue = k==0 ? 1 : 0 ; #add 1 to rowIndex and columnIndex if k=0, to accomodate for border 
                X =zeros(GenericAffExpr{BigFloat, GenericVariableRef{BigFloat}},blockSize+addValue,blockSize+addValue) #zeros(AffExpr,blockSize,blockSize) #
                for rowIndex = 1:blockSize
                    i = IndexSet[rowIndex]; 
                    for columnIndex = 1:blockSize 
                        j=  IndexSet[columnIndex];
                        for t=0:n, p=0:t
                            i4= p; i5=t-p; 
                            i3 = i-t; 
                            i2 = j-t; 
                            i1 = n-(i-t)-(j-t)-p-(t-p)
                            #t=i4+i5;p=i4; i== i3+i4+i5 && j==i2+i4+i5 
                            if i1>=0 && i2 >=0 && i3 >=0 && i4 >=0 && i5 >=0
                                X[rowIndex+addValue,columnIndex+addValue]+=alpha(n,i,j,t,p,a,k,q)*(y[orbitNumbers[[i1+i4,i2+i3+i5,0,0,0]]]-y[orbitNumbers[[i1,i2,i3,i4,i5]]])
                            end
                        end
                    end
                    if k==0 
                        X[1,rowIndex+addValue]= (y[orbitNumbers[[n,0,0,0,0]]]-y[orbitNumbers[[n-i,i,0,0,0]]])*alpha(n,i,0,0,0,0,0,q) 
                        X[rowIndex+addValue,1]= (y[orbitNumbers[[n,0,0,0,0]]]-y[orbitNumbers[[n-i,i,0,0,0]]])*alpha(n,i,0,0,0,0,0,q) 
                    end
                end
                if k==0 
                    X[1,1]=1-y[orbitNumbers[[n,0,0,0,0]]]
                end
                @constraint(model, X >=0, PSDCone())
            end
        end
    end

    #Add block-diag of Lasserre matrix corresponding the covering constraint
    for a=0:n, k=a:n 
        if k <=n+k-a 
            #Create a new block in the block diagonalization
            IndexSet, blockSize = DetermineBlockIndicesQ(n,k,a)
            if blockSize >0 
                addValue = k==0 ? 1 : 0 ; #add 1 to rowIndex and columnIndex if k=0, to accomodate for border 
                X =zeros(GenericAffExpr{BigFloat, GenericVariableRef{BigFloat}},blockSize+addValue,blockSize+addValue) #zeros(AffExpr,blockSize,blockSize)
                for rowIndex = 1:blockSize
                    i = IndexSet[rowIndex]; 
                    for columnIndex = 1:blockSize 
                        j=  IndexSet[columnIndex];
                        for p=0:n, t=p:n
                            i4= p; i5=t-p; 
                            i3 = i-t; 
                            i2 = j-t; 
                            i1 = n-(i-t)-(j-t)-p-(t-p)
                            #t=i4+i5;p=i4; i== i3+i4+i5 && j==i2+i4+i5 
                            if i1>=0 && i2 >=0 && i3 >=0 && i4 >=0 && i5 >=0
                                for supp = 0 : radius  
                                    Compositions = map(A -> [sum(A .== i) for i in 1:10], with_replacement_combinations(1:10, supp));   
                                    for eta_array in Compositions 
                                        if eta_array[1] <= i1 && eta_array[2]+eta_array[3] <= i2  && eta_array[4]+eta_array[5] <= i3 && eta_array[6]+eta_array[7] <= i4&& eta_array[8]+eta_array[9]+eta_array[10] <= i5
                                            ##we start with a triple with 000 (i1) 001 (i2) 010(i3) 011(i4) 012 (i5). 
                                            ## For i1 we get 000 -> 100 ~011, So eta_array[1] gets added to i4. 
                                            ## 001 -> 101 ~010. So eta_array[2] gets added to i3. And 001->201 ~012, so eta_array[3] gets added to i5. 
                                            ## 010 -> 110 ~001.  So eta_array[4] gets added to i2. Furthermore, 010 -> 210 ~012, so eta_array[5] gets added to i5.
                                            ## 011 -> 111 ~000. So eta_array[6] gets added to i1. Furthermore, 011->211~011, so eta_array[7] gets added to i4. 
                                            ## 012 -> 112~001, So eta_array[8] gets added to i2. Furthermore, 012->212~010 so eta_array[9] gets added to i3.  
                                            i1prime = i1-eta_array[1]+eta_array[6]; i2prime = i2-eta_array[2]-eta_array[3]+eta_array[4]+eta_array[8]
                                            i3prime = i3-eta_array[4]-eta_array[5]+eta_array[2]+eta_array[9]; i4prime = i4-eta_array[6]+eta_array[1]; i5prime = i5-eta_array[8]-eta_array[9]+eta_array[3]+eta_array[5]
                                            X[rowIndex+addValue,columnIndex+addValue]+=alpha(n,i,j,t,p,a,k,q)*y[orbitNumbers[[i1prime,i2prime,i3prime,i4prime,i5prime]]]*binomial(big(i1),eta_array[1])*multinomial(big(i2)-eta_array[2]-eta_array[3],eta_array[2],eta_array[3])*multinomial(big(i3)-eta_array[4]-eta_array[5],eta_array[4],eta_array[5])*multinomial(big(i4)-eta_array[6]-eta_array[7],eta_array[6],eta_array[7])*multinomial(big(i5)-eta_array[8]-eta_array[9]-eta_array[10],eta_array[8],eta_array[9],eta_array[10])*big((q-1))^(eta_array[1])*big(q-2)^(eta_array[3]+eta_array[5]+eta_array[7])*big(q-3)^eta_array[10]
                                        end
                                    end
                                end
                                # now we need to subtract the two-tuple. 
                                # 000 -> 000. 001 -> 001. 010 -> 110~001. 011 -> 111~000, 012->112~001. So i1=i1+i4. i2=i2+i3+i5 
                                X[rowIndex+addValue,columnIndex+addValue]-=y[orbitNumbers[[i1+i4,i2+i3+i5,0,0,0]]]*alpha(n,i,j,t,p,a,k,q)
                            end
                        end
                    end
                    if k==0 
                        i1=  n-i; i2=i ; 
                        if i1>=0 && i2 >=0 
                            for supp = 0 : radius
                                Compositions = map(A -> [sum(A .== i) for i in 1:3], with_replacement_combinations(1:3, supp));                                
                                for eta_array in Compositions 
                                    if eta_array[1] <= i1 && eta_array[2]+eta_array[3] <= i2 
                                        ##we start with a pair with 00 (i1) 01 (i2). On eta_array[1] positions out of i1 we flip the first symbol to one of the (q-1) other possible symbols.
                                        #On eta_array[2] positions out of i2 we flip the first symbol to 1, and on eta_array[3] positions out of i2 we flip the first symbol to one of the (q-2) other possible symbols
                                        i1prime = i1-eta_array[1]+eta_array[2]; i2prime = i2-eta_array[2]+eta_array[1]
                                        X[rowIndex+addValue,1]+=y[orbitNumbers[[i1prime,i2prime,0,0,0]]]*binomial(big(i1),eta_array[1])*multinomial(big(i2)-eta_array[3]-eta_array[2],eta_array[3],eta_array[2])*big(q-2)^(eta_array[3])*big(q-1)^(eta_array[1])*alpha(n,i2,0,0,0,0,0,q)#binomial(big(n),i2)*big(q-1)^i2 #alpha(n,i2,0,0,0,0,0,q)#
                                    end
                                end
                            end
                            X[rowIndex+addValue,1]-= y[orbitNumbers[[n,0,0,0,0]]]*alpha(n,i2,0,0,0,0,0,q)
                            X[1,rowIndex+addValue]= X[rowIndex+addValue,1];
                        end
                    end
                end
                if k==0
                    X[1,1]=sum([binomial(big(n),ww)*(big(q-1))^ww for ww=0:radius])*y[orbitNumbers[[n,0,0,0,0]]]-1
                end
                @constraint(model, X >=0, PSDCone())
            end
        end
    end

    ## Add linear inequalities 
    #x_{i,j}^{t,p} <= x_{i,0}^{0,0} etc
    for t=0:n, ti=0:n-t, tj=0:n-t-ti, p=0:t
        # i4= p; i5=t-p; 
        # i3 = i-t; 
        # i2 = j-t; 
        # i1 = n-(i-t)-(j-t)-p-(t-p)
        j=t+tj;i=t+ti;
        orbitNumber_i_j_t_p = orbitNumbers[[n-ti-tj-t,tj,ti,p,t-p]];
        orbitNumber_i_0_0_0 = orbitNumbers[[n-i,i,0,0,0]];
        orbitNumber_0_0_0_0 = orbitNumbers[[n,0,0,0,0]];
        orbitNumber_iplusjmintminp_0_0_0 = orbitNumbers[[n-(i+j-t-p),i+j-t-p,0,0,0]];

        @constraint(model, 1*y[orbitNumber_i_j_t_p]<=1*y[orbitNumber_i_0_0_0])
        @constraint(model, 1*y[orbitNumber_i_0_0_0]+1*y[orbitNumber_iplusjmintminp_0_0_0]-y[orbitNumber_0_0_0_0] <= y[orbitNumber_i_j_t_p])
        @constraint(model, 1*y[orbitNumber_i_j_t_p]<=1*y[orbitNumber_iplusjmintminp_0_0_0])
    end

    ##ADD LINEAR INEQUALITIES based on MATRIX CUTS for the SPHERE COVERING INEQUALIES
    for REPEAT = 1:1
        lambda = zeros(BigInt,n+1)
        betaeq = big(0) ; 

        if REPEAT==1 ## INITIALIZE SPHERE COV INEQUALITIES
            [lambda[i]=big(1) for i=1:radius+1] 
            betaeq=big(1); 
        end
        for t=0:n, ti=0:n-t, tj=0:n-t-ti, p=0:t
            # i4= p; i5=t-p; 
            # i3 = i-t; 
            # i2 = j-t; 
            # i1 = n-(i-t)-(j-t)-p-(t-p)
            j=t+tj;i=t+ti;

            coef=MakeDistrQary(n,i,j,t,p,lambda,q)
            orbitNumber_i_0_0_0 = orbitNumbers[[n-i,i,0,0,0]];
            orbitNumber_0_0_0_0 = orbitNumbers[[n,0,0,0,0]]; 

            lin1=big(0); lin2=big(0);  lin3=big(0);  lin4=big(0)

            for t2=0:n, tj2=0:n,p2=0:t2				
                    j2=t2+tj2;						
                    h=i+j2-t2-p2;
                    if n-(j2-t2)-(i-t2)-p2-(t2-p2) >=0 &&j2-t2 >=0 && i-t2 >=0 

                        orbitNumber_i_j2_t2_p2 = orbitNumbers[[n-(j2-t2)-(i-t2)-p2-(t2-p2),j2-t2,i-t2,p2,t2-p2]];
                        orbitNumber_j2_0_0_0 = orbitNumbers[[n-j2,j2,0,0,0]];
                        orbitNumber_h_0_0_0 = orbitNumbers[[n-h,h,0,0,0]]        

                        lin1+=coef[j2,t2,p2]*y[orbitNumber_i_j2_t2_p2] 

                        lin2-=coef[j2,t2,p2]*y[orbitNumber_i_j2_t2_p2] 
                        lin2+=coef[j2,t2,p2]*y[orbitNumber_j2_0_0_0]

                        lin3-=coef[j2,t2,p2]*y[orbitNumber_i_j2_t2_p2] 
                        lin3+=coef[j2,t2,p2]*y[orbitNumber_h_0_0_0]

                        lin4+=coef[j2,t2,p2]*y[orbitNumber_i_j2_t2_p2]  
                        lin4-=coef[j2,t2,p2]*y[orbitNumber_h_0_0_0]
                        lin4+=coef[j2,t2,p2]*y[orbitNumber_0_0_0_0]
                        lin4-=coef[j2,t2,p2]*y[orbitNumber_j2_0_0_0]           
                    end 
            end

            lin1-=betaeq*y[orbitNumber_i_0_0_0]

            lin2+=betaeq*y[orbitNumber_i_0_0_0]
            lin2-=betaeq*y[orbitNumber_0_0_0_0]
    
            lin3+=betaeq*y[orbitNumber_i_0_0_0]
            lin3-=betaeq*y[orbitNumber_0_0_0_0]   
            
            lin4-=betaeq   
            lin4+=2*betaeq*y[orbitNumber_0_0_0_0]
            lin4-=betaeq*y[orbitNumber_i_0_0_0]      

            @constraint(model, lin1>=0 )
            @constraint(model, lin2>=0 )
            @constraint(model, lin3>=0 )
            @constraint(model, lin4>=0 )
        end
    end

    println("starting SDP solver... ")
    println("recall (q,n,R) =  (",q,", " , n ,", ",radius,")")
    @time optimize!(model)
    
    println("scaled objective value: ", (big(q)^n*objective_value(model))^(1/3))
    return (big(q)^n*objective_value(model))^(1/3), solution_summary(model);
end