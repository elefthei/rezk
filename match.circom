pragma circom 2.0.3;

    include "utils.circom";
    include "./Nova-Scotia/circomlibs/poseidon.circom";
    
    template IsValidTrans() {
        signal input curIndex;
        signal output out;
    
        component runningProduct = MultiplierN(40);

        for (var i = 0; i < 40; i++) {
            runningProduct.in[i] <== rootsTrans(i) - curIndex;
        }
        out <== runningProduct.out;
    }
    
    template IsValidMatch() {
        signal input in;
        signal output out;
        
        component isZero = IsZero();

        component runningProduct = MultiplierN(6);
    
        for (var i = 0; i < 6; i++) {
            runningProduct.in[i] <== rootsMatch(i) - in;
        }
        isZero.in <== runningProduct.out;
        out <== isZero.out;
    }
    
    template Main () {
        signal input states[3+1];
        signal input chars[3];

        signal input step_in[3];
        signal output step_out[3];

        signal running_hash <== step_in[0];
        signal left_to_proc <==step_in[2];

        component valid_trans[3];

        component hashes[3+1];
        hashes[0] = Poseidon(1);
        hashes[0].inputs[0] <== running_hash;

        component valid_match;
        valid_match = IsValidMatch();
        
        for (var j=1;j<=3;j++) {
            valid_trans[j-1] = IsValidTrans();
            valid_trans[j-1].curIndex <== states[j-1]*10*3 + chars[j-1]*10 + states[j];
            valid_trans[j-1].out === 0;

            hashes[j] = Poseidon(2);
            hashes[j].inputs[0] <== hashes[j-1].out;
            hashes[j].inputs[1] <== chars[j-1];

        }
        valid_match.in <== states[3];

        step_out[0] <== hashes[3].out;
        step_out[1] <== valid_match.out;
        step_out[2] <== left_to_proc-3;
    }
    
    component main { public [step_in] }= Main();