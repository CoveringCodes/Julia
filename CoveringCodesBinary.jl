using JuMP, SDPAFamily, LinearAlgebra, Combinatorics
setprecision(512)

function DetermineOrbitNumbers(n)
    orbitNumbers= Dict();
    orbitNumber=0;
    ## instead of storing orbit representatives as triples [i,j,t] 
    ## in my code they are stored as quadruples [i1,i2,i3,i4], where 
    ##
    ## i1 = n-i-j+t is number of positions x000
    ## i2 = j-t     is number of positions x001 
    ## i3 = i-t     is number of positions x010
    ## i4 = t       is number of positions x011
    function numberOrbit(i,j,t)
        for tprime=0:n, iprime=0:n, jprime=0:n 
            if n>=n-iprime-jprime+tprime>=0 && n>=jprime-tprime >=0 && n>= iprime-tprime >= 0  && isequal(sort([i,j,i+j-2*t]), sort([iprime,jprime,iprime+jprime-2*tprime]))
                orbitNumbers[[n-iprime-jprime+tprime, jprime-tprime, iprime-tprime, tprime]] =orbitNumber 
            end
        end
    end

    #first number the orbits x_{i,0}^0 where i=0,...,n 
    for i=0:n 
        if !haskey(orbitNumbers, [n-i, 0, i, 0])
            orbitNumber+=1
            numberOrbit(i,0,0)
        end
    end
    for t=0:n, i=0:n, j=0:n 
        if n>=n-i-j+t>=0 && n>=j-t >=0 && n>= i-t >= 0 && !haskey(orbitNumbers, [n-i-j+t, j-t, i-t, t])
            orbitNumber+=1
            numberOrbit(i,j,t)
        end
    end
    return orbitNumbers, orbitNumber
end

function beta(n,t,i,j,k)
    return sum([(-1)^(u-t)*binomial(big(u),t)*binomial(big(n-2*k),u-k)*binomial(big(n-k-u),i-u)* binomial(big(n-k-u),j-u) for u=0:n])
end

#Given words x,y with d(x,y)=(i,j,t), calculate for each j',t' the number
#Coef[j',t']:=sum_d lambda_d*
#|words z: d(y,z)=d, d(x,z)=(i,j',t')|.
#this is needed for inequality row x around word y.
##lambda is a vector of size n+1. lambda[dist+1] corresponds with lambda_dist from the paper. 
function MakeDistr(n,i,j,t,lambda)
	ti=i-t;
	tj=j-t;
	rest=n+t-i-j;
	coef=Dict();

    #add values
	for a=0:ti, b=0:tj, c=0:t, d=0:rest
        j2=a+b+c+d;
        t2=a+c;
        dist=a+d+j-b-c;	
        if haskey(coef,(j2,t2))
            coef[j2,t2]+=lambda[dist+1]*binomial(big(ti),a)*binomial(big(tj),b)*binomial(big(t),c)*binomial(big(rest),d)
        else
            coef[j2,t2]=lambda[dist+1]*binomial(big(ti),a)*binomial(big(tj),b)*binomial(big(t),c)*binomial(big(rest),d)
        end
    end         
	return coef;
end

function DetermineBlockIndices(n,k,d=0) 
    IndexSet=[]
    for r =k:n-k
        if  (((n-r) ==0 || (n-r)>=d))    
            push!(IndexSet,r);
        end
    end
    return IndexSet, size(IndexSet,1)
end

function CoveringCodesBinary(n,R)
    orbitNumbers, nVars = DetermineOrbitNumbers(n);

    opt = SDPAFamily.Optimizer(variant= :sdpa_gmp,verbose=SDPAFamily.VERBOSE,
    presolve = true, silent=false,
    params = (  lambdaStar=1e10, epsilonStar = 1e-20, betaStar=0.2, betaBar=0.4, gammaStar=0.6,# constraint tolerance
                epsilonDash = 1e-20, upperBound=1e17, lowerBound=-1e17, maxIteration=600, precision=512 # arithmetric precision used in sdpa_gmp
    ))

    model =GenericModel{BigFloat}()
    set_optimizer(model, () -> opt)
    @variable(model, y[1:nVars])

    for i=1:nVars
        @constraint(model, y[i]>=0)
    end

    objectivepoly = 0; 
    for i2=0:n,i3=0:n-i2,i4=0:n-i2-i3
        objectivepoly += multinomial(big(i2),big(i3),big(i4),big(n-i2-i3-i4))*y[orbitNumbers[[n-i2-i3-i4,i2,i3,i4]]]
    end
    @objective(model,Min,objectivepoly)

    println("Generating semidefinite constraints...")
    #add block-diag of first semidefinite constraint, matrix M' from paper
    for k=0:Int(floor(n/2))
        #Create a new block in the block diagonalization
        IndexSet, blockSize = DetermineBlockIndices(n,k)
        if blockSize >0 
            X =zeros(GenericAffExpr{BigFloat, GenericVariableRef{BigFloat}},blockSize,blockSize) #zeros(AffExpr,blockSize,blockSize) #
            for rowIndex = 1:blockSize
                for columnIndex = 1:blockSize 
                    r1 = IndexSet[rowIndex]; 
                    r2 = IndexSet[columnIndex];
                    i=n-r1; j=n-r2; 
                    for t=0:n
                        i1=  n-j-i+t; i2= j-t; i3= i-t; i4=t ; 
                        if i1>=0 && i2 >=0 && i3 >=0 && i4 >=0 
                            X[rowIndex,columnIndex]+=y[orbitNumbers[[i1,i2,i3,i4]]]*beta(n,t,i,j,k)
                        end
                    end
                end
            end
            @constraint(model, X >=0, PSDCone())
        end
    end

    #add block-diag of second semidefinite constraint, matrix M'' with border from paper
    for k=0:Int(floor(n/2))
        #Create a new block in the block diagonalization
        IndexSet, blockSize = DetermineBlockIndices(n,k)
        if blockSize >0 
            addValue = k==0 ? 1 : 0 ; #add 1 to rowIndex and columnIndex if k=0, to accomodate for border 
            X =zeros(GenericAffExpr{BigFloat, GenericVariableRef{BigFloat}},blockSize+addValue,blockSize+addValue) #zeros(AffExpr,blockSize,blockSize) #
            for rowIndex = 1:blockSize
                r1 = IndexSet[rowIndex]; 
                i=n-r1;
                for columnIndex = 1:blockSize 
                    r2= IndexSet[columnIndex];
                    j=n-r2; 
                    for t=0:n
                        i1=  n-j-i+t; i2= j-t; i3= i-t; i4=t ; 
                        if i1>=0 && i2 >=0 && i3 >=0 && i4 >=0 
                            X[rowIndex+addValue,columnIndex+addValue]+=(y[orbitNumbers[[i1+i4,i2+i3,0,0]]]-y[orbitNumbers[[i1,i2,i3,i4]]])*beta(n,t,i,j,k)
                        end
                    end
                end
                if k==0 
                   X[1,rowIndex+addValue]= binomial(big(n),i)*(y[orbitNumbers[[n,0,0,0]]]-y[orbitNumbers[[n-i,i,0,0]]]);
                   X[rowIndex+addValue,1]= binomial(big(n),i)*(y[orbitNumbers[[n,0,0,0]]]-y[orbitNumbers[[n-i,i,0,0]]]);
                end
            end
            if k==0 
                X[1,1]=1-y[orbitNumbers[[n,0,0,0]]]
            end
            @constraint(model, X >=0, PSDCone())
        end
    end

    println("Generating Lasserre constraints...")
    #add block-diag of Lasserre matrices corresponding to covering constraint and Van Wee constraint
    for REPEAT = 1:2
        lambda = zeros(BigInt,n+1)
        betaeq = big(0);
        maxLambdaINonZero=0 

        if REPEAT==1 ## INITIALIZE SPHERE COV INEQUALITIES
            [lambda[i]=big(1) for i=1:R+1] 
            betaeq=big(1); 
            maxLambdaINonZero=R 
        elseif REPEAT==2 ## INITIALIZE VAN WEE
            for i=0:R-1 
                lambda[i+1]=big(Int(ceil((n+1)/(R+1))))
            end
            lambda[R+1]=1; lambda[R+2]=1; 
            betaeq = big(Int(ceil((n+1)/(R+1))))    
            maxLambdaINonZero=R+1
        end
        for k=0:Int(floor(n/2))
            #Create a new block in the block diagonalization
            IndexSet, blockSize = DetermineBlockIndices(n,k)
            if blockSize >0 
                addValue = k==0 ? 1 : 0 ; #add 1 to rowIndex and columnIndex if k=0, to accomodate for border 
                X =zeros(GenericAffExpr{BigFloat, GenericVariableRef{BigFloat}},blockSize+addValue,blockSize+addValue) #zeros(AffExpr,blockSize,blockSize) #
                for rowIndex = 1:blockSize
                    r1 = IndexSet[rowIndex];
                    i=n-r1; 
                    for columnIndex = 1:blockSize 
                        r2 = IndexSet[columnIndex];
                        j=n-r2; 
                        for t=0:n
                            i1=  n-j-i+t; i2= j-t; i3= i-t; i4=t ; 
                            if i1>=0 && i2 >=0 && i3 >=0 && i4 >=0 
                                for supp = 0 : maxLambdaINonZero
                                    Compositions = map(A -> [sum(A .== i) for i in 1:4], with_replacement_combinations(1:4, supp));                                
                                    for eta_array in Compositions 
                                        if eta_array[1] <= i1 && eta_array[2] <= i2  && eta_array[3] <= i3  && eta_array[4] <= i4 
                                            ##we start with a triple with 000 (i1) 001 (i2) 010(i3) 011(i4). On eta_array[1] positions out of i1, eta_array[2] positions out of i2, eta_array[3] positions out of i3, eta_array[4] positions out of i4, we will flip the first bit. 
                                            ## 000 -> 100 ~ 011.  
                                            ## 001 -> 101 ~ 010. 
                                            ## 010 -> 110 ~ 001.  
                                            ## 011 -> 111 ~ 000. 
                                            i1prime = i1-eta_array[1]+eta_array[4]; i2prime = i2-eta_array[2]+eta_array[3]
                                            i3prime = i3-eta_array[3]+eta_array[2]; i4prime = i4-eta_array[4]+eta_array[1]; 
                                            X[rowIndex+addValue,columnIndex+addValue]+=lambda[supp+1]*y[orbitNumbers[[i1prime,i2prime,i3prime,i4prime]]]*beta(n,t,i,j,k)*binomial(big(i1),eta_array[1])*binomial(big(i2),eta_array[2])*binomial(big(i3),eta_array[3])*binomial(big(i4),eta_array[4])
                                        end
                                    end
                                end
                                ##now we need to subtract the two-tuple. 
                                ##000 -> 000. 001 -> 001. 010 -> 110~001. 011 -> 111~000. So i1=i1+i4. i2=i2+i3 
                                X[rowIndex+addValue,columnIndex+addValue]-=betaeq*y[orbitNumbers[[i1+i4,i2+i3,0,0]]]*beta(n,t,i,j,k)
                            end
                        end 
                    end
                    if k==0 
                        i1=  n-i; i2=i ; 
                        if i1>=0 && i2 >=0 
                            for supp = 0 : maxLambdaINonZero
                                Compositions = map(A -> [sum(A .== i) for i in 1:2], with_replacement_combinations(1:2, supp));                                
                                for eta_array in Compositions 
                                    if eta_array[1] <= i1 && eta_array[2] <= i2 
                                        ##we start with a pair with 000 (i1) 001 (i2). On eta_array[1] positions out of i1, eta_array[2] positions out of i2, we will flip the first bit. 
                                        ## 000 -> 100 ~ 011.  
                                        ## 001 -> 101 ~ 010. 
                                        i1prime = i1-eta_array[1]+eta_array[2]; i2prime = i2-eta_array[2]+eta_array[1]
                                        X[rowIndex+addValue,1]+=lambda[supp+1]*y[orbitNumbers[[i1prime,i2prime,0,0]]]*binomial(big(i1),eta_array[1])*binomial(big(i2),eta_array[2])*binomial(big(n),i2)
                                    end
                                end
                            end
                            X[rowIndex+addValue,1]-= betaeq*y[orbitNumbers[[n,0,0,0]]]*binomial(big(n),i2)
                            X[1,rowIndex+addValue]=X[rowIndex+addValue,1];
                        end
                    end
                end
                if k==0 
                    X[1,1]=sum([binomial(big(n),ww)*lambda[ww+1] for ww=0:maxLambdaINonZero])*y[orbitNumbers[[n,0,0,0]]]-betaeq
                end
                @constraint(model, X >=0, PSDCone())
            end
        end
    end

    println("Generating linear inequalities...")
    ## Add linear inequalities 
    for t=0:n, ti=0:n-t, tj=0:n-t-ti
        j=t+tj;i=t+ti;

        orbitNumber_i_j_t = orbitNumbers[[n-ti-tj-t,tj,ti,t]];
        orbitNumber_i_0_0 = orbitNumbers[[n-i,i,0,0]];
        orbitNumber_0_0_0 = orbitNumbers[[n,0,0,0]];
        orbitNumber_iplusj2t_0_0 = orbitNumbers[[n-(i+j-2*t),i+j-2*t,0,0]];

        @constraint(model, 1*y[orbitNumber_i_j_t]<=1*y[orbitNumber_i_0_0])
        @constraint(model, 1*y[orbitNumber_i_0_0]+1*y[orbitNumber_iplusj2t_0_0]-y[orbitNumber_0_0_0] <= y[orbitNumber_i_j_t])
        @constraint(model, 1*y[orbitNumber_i_j_t]<=1*y[orbitNumber_iplusj2t_0_0])
    end

    ## Add linear inequalities  based on MATRIX CUTS, for the Sphere covering and Van Wee inequalities
    for REPEAT = 1:2 
        lambda = zeros(BigInt,n+1)
        betaeq = big(0) ; 

        if REPEAT==1 ## INITIALIZE SPHERE COV INEQUALITIES
            [lambda[i]=big(1) for i=1:R+1] 
            betaeq=big(1); 
        elseif REPEAT==2 ## INITIALIZE VAN WEE
            for i=0:R-1 
                lambda[i+1]=big(Int(ceil((n+1)/(R+1))))
            end
            lambda[R+1]=1; lambda[R+2]=1; 
            betaeq = big(Int(ceil((n+1)/(R+1))))
        end
        for t=0:n, ti=0:n-t, tj=0:n-t-ti
            j=t+tj;i=t+ti;
            coef=MakeDistr(n,i,j,t,lambda)
            orbitNumber_i_0_0 = orbitNumbers[[n-i,i,0,0]]; 
            orbitNumber_0_0_0 = orbitNumbers[[n,0,0,0]];        

            lin1=big(0); lin2=big(0);  lin3=big(0);  lin4=big(0)

            for t2=0:min(n,i), tj2=0:n-i				
                j2=t2+tj2;						
                h=i+j2-2*t2;
                
                orbitNumber_i_j2_t2 = orbitNumbers[[n-(j2-t2)-(i-t2)-t2,j2-t2,i-t2,t2]];
                orbitNumber_j2_0_0 = orbitNumbers[[n-j2,j2,0,0]];
                orbitNumber_h_0_0 = orbitNumbers[[n-h,h,0,0]]        

                lin1+=coef[j2,t2]*y[orbitNumber_i_j2_t2]

                lin2-=coef[j2,t2]*y[orbitNumber_i_j2_t2]
                lin2+=coef[j2,t2]*y[orbitNumber_j2_0_0]

                lin3-=coef[j2,t2]*y[orbitNumber_i_j2_t2]
                lin3+=coef[j2,t2]*y[orbitNumber_h_0_0]

                lin4+=coef[j2,t2]*y[orbitNumber_i_j2_t2]
                lin4-=coef[j2,t2]*y[orbitNumber_h_0_0]
                lin4+=coef[j2,t2]*y[orbitNumber_0_0_0]
                lin4-=coef[j2,t2]*y[orbitNumber_j2_0_0]            
            end

            lin1-=betaeq*y[orbitNumber_i_0_0]

            lin2+=betaeq*y[orbitNumber_i_0_0]
            lin2-=betaeq*y[orbitNumber_0_0_0]
    
            lin3+=betaeq*y[orbitNumber_i_0_0]
            lin3-=betaeq*y[orbitNumber_0_0_0]   
            
            lin4-=betaeq   
            lin4+=2*betaeq*y[orbitNumber_0_0_0]
            lin4-=betaeq*y[orbitNumber_i_0_0]      

            @constraint(model, lin1>=0 )
            @constraint(model, lin2>=0 )
            @constraint(model, lin3>=0 )
            @constraint(model, lin4>=0 )
        end
    end

    println("starting SDP solver... ")
    println("recall (n,R) =  (" , n ,", ",R,")")
    @time optimize!(model)
    println("scaled objective value: ", (objective_value(model)*big(2)^n)^(1/3))

    return (objective_value(model)*big(2)^n)^(1/3), solution_summary(model);
end