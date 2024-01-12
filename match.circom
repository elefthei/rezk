pragma circom 2.0.3;

    include "utils.circom";
    include "./Nova-Scotia/circomlibs/poseidon.circom";
    
    template IsValidTrans() {
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN(10);

        for (var i = 0; i < 10; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    template IsValidMatch() {
        signal input in;
        signal output out;
        
        component isZero = IsZero();

        component runningProduct = MultiplierN(2);
    
        for (var i = 0; i < 2; i++) {
            runningProduct.in[i] <== rootsMatch(i) - in;
        }
        isZero.in <== runningProduct.out;
        out <== isZero.out;
    }
    
    template Main () {
        signal input states[2+1];
        signal input chars[2];

        signal input step_in[4];
        signal output step_out[4];

        signal running_hash <== step_in[0];
        signal left_to_proc <==step_in[2];

        component valid_trans[2];

        component hashes[2+1];
        hashes[0] = Poseidon(1);
        hashes[0].inputs[0] <== running_hash;

        component valid_match;
        valid_match = IsValidMatch();

        var loop = 2+1;
        
        for (var j=1;j<loop;j++) {
            valid_trans[j-1] = IsValidTrans();
            valid_trans[j-1].curIndex <== states[j-1]*5*1 + chars[j-1]*5 + states[j];
            valid_trans[j-1].out === 0;

            hashes[j] = Poseidon(2);
            hashes[j].inputs[0] <== hashes[j-1].out;
            hashes[j].inputs[1] <== chars[j-1];

        }
        valid_match.in <== states[2];

        step_out[0] <== hashes[2].out;
        step_out[1] <== valid_match.out;
        step_out[2] <== left_to_proc-2;
        step_out[3] <== 0;
    }
    
    component main { public [step_in] }= Main();