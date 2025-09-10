#include "pol_verifier.h"
#include "config_pc.hpp"
#include "GKR.h"
#include "mimc.h"


int gkr_proof_size(struct proof P){
	int size = 0;
	for(int i = 0; i < P.q_poly.size(); i++){
		size+=3;
	}
	for(int i = 1; i < P.randomness.size(); i++){
		for(int j = 0; j < P.randomness[i].size(); j++){
			size++;
		}
	}
	for(int i = 0; i < P.sig.size(); i++){
		for(int j = 0; j < P.sig[i].size(); j++){
			size+=2;
		}
	}
	for(int i = 0; i < P.vr.size(); i++){
		size+=2;
	}
	return size*32;
}

vector<F> encode_gkr_proof(struct proof P){
	vector<F> data;
	for(int i = 0; i < P.q_poly.size(); i++){
		data.push_back(P.q_poly[i].a);
		data.push_back(P.q_poly[i].b);
		data.push_back(P.q_poly[i].c);
	}
	for(int i = 1; i < P.randomness.size(); i++){
		for(int j = 0; j < P.randomness[i].size(); j++){
			data.push_back(P.randomness[i][j]);
		}
	}

	/*
	for(int i = 0; i < P.w_hashes.size(); i++){
		for(int j = 0; j < P.w_hashes[i].size(); j++){
			for(int k = 0; k < P.w_hashes[i][j].size(); k++){
				data.push_back(P.w_hashes[i][j][k]);
			}
		}
	}
	*/
	
	for(int i = 0; i < P.sig.size(); i++){
		for(int j = 0; j < P.sig[i].size(); j++){
			data.push_back(P.sig[i][j]);
			data.push_back(P.final_claims_v[i][j]);
		}
	}
	for(int i = 0; i < P.vr.size(); i++){
		data.push_back(P.vr[i]);
		data.push_back(P.gr[i]);	
	}
	data.push_back(P.q_poly[0].eval(0) + P.q_poly[0].eval(1));
	return data;
}

std::vector<int> get_gkr_transcript(const proof& P) {
    std::vector<int> tr;
    // Layout: [TYPE, levels, |rand[1]|, |rand[2]|, ..., |sig[0]|, |sig[1]|, ...]
    const size_t extra_rand = (P.randomness.size() > 1) ? (P.randomness.size() - 1) : 0;
    tr.reserve(2 + extra_rand + P.sig.size());

    // Type tag
    tr.push_back(GKR_PROOF);

    // levels = max(|randomness|-1, 0)  (avoid negative when randomness is empty)
    int levels = static_cast<int>(P.randomness.size());
    levels = (levels > 0) ? (levels - 1) : 0;
    tr.push_back(levels);

    // Sizes of randomness vectors starting from index 1
    for (size_t i = 1; i < P.randomness.size(); ++i) {
        tr.push_back(static_cast<int>(P.randomness[i].size()));
    }

    // Sizes of signature vectors
    for (size_t i = 0; i < P.sig.size(); ++i) {
        tr.push_back(static_cast<int>(P.sig[i].size()));
    }

    return tr;
}

int m2m_size(struct proof P){
	int size = 0;
	for(int i = 0; i < P.q_poly.size(); i++){
		size+= 3;
	}
	for(int i = 0; i < P.randomness[0].size(); i++){
		size++;
	}
	return (size+1)*32;
}


std::vector<F> encode_m2m_proof(struct proof P){
    std::vector<F> data;
    data.reserve(3 * P.q_poly.size()
                 + (P.randomness.empty() ? 0 : (int)P.randomness[0].size())
                 + 3);

    for (int i = 0; i < P.q_poly.size(); ++i){
        data.push_back(P.q_poly[i].a);
        data.push_back(P.q_poly[i].b);
        data.push_back(P.q_poly[i].c);
    }
    if (!P.randomness.empty()){
        for (int i = 0; i < P.randomness[0].size(); ++i)
            data.push_back(P.randomness[0][i]);
    }
    data.push_back(P.vr[0]);
    data.push_back(P.vr[1]);
    data.push_back(P.q_poly[0].eval(0) + P.q_poly[0].eval(1));
    return data;
}

vector<F> encode_hash_proof(proof P){
	vector<F> data;
	for(int i = 0; i < P.quad_poly.size(); i++){
		data.push_back(P.quad_poly[i].a);
		data.push_back(P.quad_poly[i].b);
		data.push_back(P.quad_poly[i].c);	
		data.push_back(P.quad_poly[i].d);	
		data.push_back(P.quad_poly[i].e);	
	}
	
	for(int i = 0; i < P.randomness[0].size(); i++){
		data.push_back(P.randomness[0][i]);
	}
	data.push_back(P.vr[0]);
	data.push_back(P.vr[1]);
	data.push_back(P.quad_poly[0].eval(0) + P.quad_poly[0].eval(1));
	return data;
}

std::vector<F> encode_lookup_proof(layer_proof P){
    std::vector<F> data;
    data.reserve(4 * P.c_poly.size()
                 + (P.randomness.empty() ? 0 : (int)P.randomness[0].size())
                 + 3);

    for (int i = 0; i < P.c_poly.size(); ++i){
        data.push_back(P.c_poly[i].a);
        data.push_back(P.c_poly[i].b);
        data.push_back(P.c_poly[i].c);
        data.push_back(P.c_poly[i].d);
    }
    if (!P.randomness.empty()){
        for (int i = 0; i < P.randomness[0].size(); ++i)
            data.push_back(P.randomness[0][i]);
    }
    data.push_back(P.vr[0]);
    data.push_back(P.vr[1]);
    data.push_back(P.q_poly[0].eval(0) + P.q_poly[0].eval(1));
    return data;
}


std::vector<int> get_hash_transcript(struct proof P) {
    std::vector<int> tr;
    tr.reserve(2);
    tr.push_back(HASH_SUMCHECK);
    int r0 = (!P.randomness.empty()) ? (int)P.randomness[0].size() : 0;
    tr.push_back(r0);
    return tr;
}

std::vector<int> get_m2m_transcript(struct proof P) {
    std::vector<int> tr;
    tr.reserve(2);
    tr.push_back(MATMUL_PROOF);
    int r0 = (!P.randomness.empty()) ? (int)P.randomness[0].size() : 0;
    tr.push_back(r0);
    return tr;
}

std::vector<int> get_lookup_transcript(layer_proof P) {
    std::vector<int> tr;
    tr.reserve(2);
    tr.push_back(LOOKUP_PROOF);
    int r0 = (!P.randomness.empty()) ? (int)P.randomness[0].size() : 0;
    tr.push_back(r0);
    return tr;
}


int bit_decomposition_size(const proof& P){
    int size = 0;
    size += 3 * static_cast<int>(P.q_poly.size());
    size += 4 * static_cast<int>(P.c_poly.size());

    int r2 = (P.randomness.size() > 2) ? static_cast<int>(P.randomness[2].size()) : 0;
    int r3 = (P.randomness.size() > 3) ? static_cast<int>(P.randomness[3].size()) : 0;
    size += r2 + r3;

    size += 1; // keep existing logic
    if (P.type == RANGE_PROOF_OPT) {
        // (left empty in your code; keep behavior)
    }
    return size * 32;
}

std::vector<F> encode_bit_decomposition(const proof& P){
    std::vector<F> data;

    for (int i = 0; i < P.q_poly.size(); ++i){
        data.push_back(P.q_poly[i].a);
        data.push_back(P.q_poly[i].b);
        data.push_back(P.q_poly[i].c);
    }
    for (int i = 0; i < P.c_poly.size(); ++i){
        data.push_back(P.c_poly[i].a);
        data.push_back(P.c_poly[i].b);
        data.push_back(P.c_poly[i].c);
        data.push_back(P.c_poly[i].d);
    }

    if (P.randomness.size() > 2){
        for (int i = 0; i < P.randomness[2].size(); ++i)
            data.push_back(P.randomness[2][i]);
    }
    if (P.randomness.size() > 3){
        for (int i = 0; i < P.randomness[3].size(); ++i)
            data.push_back(P.randomness[3][i]);
    }

    auto vr_at = [&](size_t idx)->F {
        return (P.vr.size() > idx) ? P.vr[idx] : F(0);
    };

    data.push_back(vr_at(0));
    data.push_back(vr_at(1));
    data.push_back(vr_at(2));
    data.push_back(F(1) - vr_at(2));
    data.push_back(vr_at(3));

    F q0 = (P.q_poly.size() > 0) ? (P.q_poly[0].eval(0) + P.q_poly[0].eval(1)) : F(0);
    data.push_back(q0);

    return data;
}

vector<int> get_range_proof_transcript(struct proof P){
	int arr[3];
	arr[0] = RANGE_PROOF;
	arr[1] = P.randomness[2].size();
	arr[2] = P.randomness[3].size();
	vector<int> tr;
	for(int i = 0; i < 3; i++){
		tr.push_back(arr[i]);
	}

	return tr;
}


void verify_gkr(struct proof P){
	
	char buff[256];
	vector<F> output_randomness = P.randomness[0];
	vector<F> sumcheck_randomness;
	
	for(int i = 1; i < P.randomness.size(); i++){
		for(int j = 0; j < P.randomness[i].size(); j++){
			sumcheck_randomness.push_back(P.randomness[i][j]);
		}
	}

	int layers = ((P.randomness).size()-1)/3;
	
	F temp_sum = F(P.q_poly[0].eval(0) + P.q_poly[0].eval(1));
	int counter = 1;
	int poly_counter = 0;
	
	for(int i = 0; i < layers; i++){
		for(int j = 0; j < P.randomness[counter].size(); j++){
			//printf("%d\n",j );
			if(temp_sum != P.q_poly[poly_counter].eval(0) + P.q_poly[poly_counter].eval(1)){
				printf("Error in sumcheck 1 %d %d\n",i,j );
				exit(-1);
			}

			temp_sum = P.q_poly[poly_counter].eval(sumcheck_randomness[poly_counter]);
			poly_counter += 1;
			vector<F> in;
			in.push_back(temp_sum);
			in.push_back(P.q_poly[poly_counter].a);
			in.push_back(P.q_poly[poly_counter].b);
			in.push_back(P.q_poly[poly_counter].c);
			mimc_multihash(in);
		}


		counter += 1;
		for(int j = 0; j < P.randomness[counter].size(); j++){
			if(temp_sum != P.q_poly[poly_counter].eval(0) + P.q_poly[poly_counter].eval(1)){
				printf("Error in sumcheck 2 %d\n",i );
				exit(-1);
			}
			temp_sum = P.q_poly[poly_counter].eval(sumcheck_randomness[poly_counter]);
			poly_counter += 1;
			vector<F> in;
			in.push_back(temp_sum);
			in.push_back(P.q_poly[poly_counter].a);
			in.push_back(P.q_poly[poly_counter].b);
			in.push_back(P.q_poly[poly_counter].c);
			mimc_multihash(in);
		}
		temp_sum = F(0);
		//printf("%d\n", P.sig );
		//printf("%d\n",P.sig[i].size() );
		for(int j = 0; j < P.sig[i].size(); j++){
			temp_sum += P.sig[i][j]*P.final_claims_v[i][j];
		}
		//temp_sum = P.liu_sum[i];
		counter += 1;

		for(int j = 0; j < P.randomness[counter].size(); j++){
			if(temp_sum != P.q_poly[poly_counter].eval(0) + P.q_poly[poly_counter].eval(1)){
				printf("Error in sumcheck 3 %d\n",i );
				exit(-1);
			}
			temp_sum = P.q_poly[poly_counter].eval(sumcheck_randomness[poly_counter]);
			poly_counter += 1;
			vector<F> in;
			in.push_back(temp_sum);
			in.push_back(P.q_poly[poly_counter].a);
			in.push_back(P.q_poly[poly_counter].b);
			in.push_back(P.q_poly[poly_counter].c);
			mimc_multihash(in);
		}
		if(temp_sum != P.vr[i]*P.gr[i]){
			printf("Error in final check %d\n",i);
			exit(-1);
		}
		temp_sum = P.vr[i];
		
		counter+=1;

	}
}



void verify_matrix2matrix(struct proof Pr){
	vector<quadratic_poly> Polynomials = Pr.q_poly;
	vector<F> r = Pr.randomness[0];
	
	/*if(M.size() == 0){
		M = matrix2matrix(M1,M2);
	}
	F eval = evaluate_matrix(M,Pr.randomness[1],Pr.randomness[2]);
	// Remove the bias evaluation
	if(b.size() != 0){
		eval = eval - evaluate_vector(b,Pr.randomness[1]);
	}
	if(eval == Polynomials[0].eval(0) + Polynomials[0].eval(1)){
		printf("Matrix2matrix sumcheck Correct\n");
	}
	else{
		printf("Incorrect product\n");
		exit(-1);
	}
	*/
	F sum = Polynomials[0].eval(r[0]);
	for(int i = 1; i < Polynomials.size(); i++){
		if(Polynomials[i].eval(0) + Polynomials[i].eval(1) != sum){
			printf("Error in sumcheck matmul\n");
			exit(-1);
		}
		vector<F> in;
		in.push_back(sum);
		in.push_back(Polynomials[i].a);
		in.push_back(Polynomials[i].b);
		in.push_back(Polynomials[i].c);
		mimc_multihash(in);
		sum = Polynomials[i].eval(r[i]);
	}
	if(sum != Pr.vr[0]*Pr.vr[1]){
		printf("Error in final matmul\n");
		exit(-1);
	}
}


void verify_bit_decomposition(struct proof Pr){
	vector<quadratic_poly> poly1 = Pr.q_poly;
	vector<cubic_poly> poly2 = Pr.c_poly;
	//F eval = evaluate_vector(num,Pr.randomness[0]);
	F sum2 = F(0);
	if(Pr.type == RANGE_PROOF_OPT){
	}

	if(sum2 != poly2[0].eval(0) + poly2[0].eval(1)){
		printf("Error in verifying bit decomposition\n");
		exit(-1);
	}
	
	vector<F> r = Pr.randomness[2];
	F sum = poly1[0].eval(r[0]);
	for(int i = 1; i < poly1.size(); i++){
		if(poly1[i].eval(0) + poly1[i].eval(1) != sum){
			printf("Error in range proof sumcheck 1\n");
			exit(-1);
		}
		sum = poly1[i].eval(r[i]);
		vector<F> in;
		in.push_back(r[i]);
		in.push_back(poly1[i].a);
		in.push_back(poly1[i].b);
		in.push_back(poly1[i].c);
		mimc_multihash(in);

	}
	if(sum != Pr.vr[0]*Pr.vr[1]){
		printf("Error in bit decomposition final 1\n");
		exit(-1);
	}
	r = Pr.randomness[3];
	sum = poly2[0].eval(r[0]);
	for(int i = 1; i < poly2.size(); i++){
		if(poly2[i].eval(0) + poly2[i].eval(1) != sum){
			printf("Error in range proof sumcheck 2\n");
			exit(-1);
		}
		vector<F> in;
		in.push_back(r[i]);
		in.push_back(poly2[i].a);
		in.push_back(poly2[i].b);
		in.push_back(poly2[i].c);
		in.push_back(poly2[i].d);
		mimc_multihash(in);

		sum = poly2[i].eval(r[i]);
	}
	if(sum != Pr.vr[2]*(F(1)-Pr.vr[2])*Pr.vr[3]){
		printf("Error in bit decomposition final 2\n");
		exit(-1);
	}
}

void write_transcript(const std::vector<std::vector<int>>& tr, const char* name) {
    if (name == nullptr) {
        fprintf(stderr, "write_transcript: name is null\n");
        return;
    }

    FILE* f = fopen(name, "w+");
    if (!f) {
        perror("write_transcript: fopen");
        fprintf(stderr, "  path: %s\n", name);
        return;
    }

    for (size_t i = 0; i < tr.size(); ++i) {
        for (size_t j = 0; j < tr[i].size(); ++j) {
            if (fprintf(f, "%d ", tr[i][j]) < 0) {
                perror("write_transcript: fprintf");
                fclose(f);
                return;
            }
        }
        if (fprintf(f, "\n") < 0) {
            perror("write_transcript: fprintf newline");
            fclose(f);
            return;
        }
    }

    fprintf(f, "\n");
    fclose(f);
}

void write_proof_data(const std::vector<std::vector<F>>& data, const char* name) {
    if (!name) { fprintf(stderr, "write_proof_data: name is null\n"); return; }
    FILE* f = fopen(name, "w");
    if (!f) { perror("write_proof_data: fopen"); fprintf(stderr, "  path: %s\n", name); return; }

    size_t counter = 0;
    for (size_t i = 0; i < data.size(); ++i) {
        for (size_t j = 0; j < data[i].size(); ++j) {
            std::string s = data[i][j].toString();  // copy to avoid reused static buffer
            if (fprintf(f, "%s\n", s.c_str()) < 0) { perror("write_proof_data: fprintf"); fclose(f); return; }
            ++counter;
        }
    }

    std::string one = F(1).toString();
    if (fprintf(f, "%s\n", one.c_str()) < 0) { perror("write_proof_data: fprintf tail"); fclose(f); return; }
    ++counter;

    // Optional debug: fprintf(stderr, "%zu\n", counter);
    fclose(f);
}

// Safer write_proof_data_hashes: prints all field elements, then a trailing "0"
void write_proof_data_hashes(const std::vector<std::vector<F>>& data, const char* name) {
    if (!name) { fprintf(stderr, "write_proof_data_hashes: name is null\n"); return; }
    FILE* f = fopen(name, "w");
    if (!f) { perror("write_proof_data_hashes: fopen"); fprintf(stderr, "  path: %s\n", name); return; }

    size_t counter = 0;
    for (size_t i = 0; i < data.size(); ++i) {
        for (size_t j = 0; j < data[i].size(); ++j) {
            std::string s = data[i][j].toString();
            if (fprintf(f, "%s\n", s.c_str()) < 0) { perror("write_proof_data_hashes: fprintf"); fclose(f); return; }
            ++counter;
        }
    }

    std::string zero = F(0).toString();
    if (fprintf(f, "%s\n", zero.c_str()) < 0) { perror("write_proof_data_hashes: fprintf tail"); fclose(f); return; }
    ++counter;

    // Optional debug: fprintf(stderr, "%zu\n", counter);
    fclose(f);
}


struct proof verify_hashes(vector<struct proof> P){
	vector<vector<int>> transcript;
	vector<vector<F>> data;
	for(int i = 0; i < P.size(); i++){
		if(P[i].type == MATMUL_PROOF){
			verify_matrix2matrix(P[i]);
			data.push_back(encode_m2m_proof(P[i]));
			transcript.push_back(get_m2m_transcript(P[i]));
		}
		else if(P[i].type == RANGE_PROOF){
			verify_bit_decomposition(P[i]);
			data.push_back(encode_bit_decomposition(P[i]));
			transcript.push_back(get_range_proof_transcript(P[i]));
		}else if(P[i].type == LOOKUP_PROOF){
			for(int j =  0; j < P[i].proofs.size(); j++){
				data.push_back(encode_lookup_proof(P[i].proofs[j]));
				transcript.push_back(get_lookup_transcript(P[i].proofs[j]));
			}
		}else if(P[i].type == HASH_SUMCHECK){
			data.push_back(encode_hash_proof(P[i]));
			transcript.push_back(get_hash_transcript(P[i]));
		}
		else if(P[i].type == GKR_PROOF){
			verify_gkr(P[i]);
			data.push_back(encode_gkr_proof(P[i]));
			transcript.push_back(get_gkr_transcript(P[i]));
		}
	}
	data.push_back(get_parameters());
	
	//data.push_back(F())
	string filename = "hashes_input";
	char name[filename.length()+1];
	strcpy(name, filename.c_str());
	string circuit_filename = "hashes_transcript";
	char transcript_name[circuit_filename.length()+1];
	strcpy(transcript_name, circuit_filename.c_str());
	write_transcript(transcript,transcript_name);
	
	vector<F> gkr_data;
	for(int i = 0; i < data.size(); i++){
		for(int j = 0; j <data[i].size(); j++){
			gkr_data.push_back(data[i][j]);
		}
	}
	gkr_data.push_back(F(0));

	//write_proof_data_hashes(data,name);
	circuit_filename = "hash_function_eval.pws";
	char circuit_name[circuit_filename.length()+1];
	strcpy(circuit_name, circuit_filename.c_str());
	vector<F> r(10);
	for(int i = 0; i < 10; i++){
		r[i] = random();//.setByCSPRNG();
	}
	return prove_hash_verification(gkr_data,r,transcript);
	//generate_GKR_proof(circuit_name,name,r,false);
}

struct proof verify_proof(vector<proof> proofs){
	
	vector<vector<int>> transcript;
	vector<vector<F>> data;
	for(int i = 0; i < proofs.size(); i++){
		if(proofs[i].type == MATMUL_PROOF){
			verify_matrix2matrix(proofs[i]);
			data.push_back(encode_m2m_proof(proofs[i]));
			transcript.push_back(get_m2m_transcript(proofs[i]));
		}else if(proofs[i].type == LOOKUP_PROOF){
			for(int j =  0; j < proofs[i].proofs.size(); j++){
				data.push_back(encode_lookup_proof(proofs[i].proofs[j]));
				transcript.push_back(get_lookup_transcript(proofs[i].proofs[j]));
			}
		
		}else if(proofs[i].type == HASH_SUMCHECK){
			data.push_back(encode_hash_proof(proofs[i]));
			transcript.push_back(get_hash_transcript(proofs[i]));
		}
		else if(proofs[i].type == RANGE_PROOF){
			verify_bit_decomposition(proofs[i]);
			data.push_back(encode_bit_decomposition(proofs[i]));
			transcript.push_back(get_range_proof_transcript(proofs[i]));
		}
		else if(proofs[i].type == GKR_PROOF){
			verify_gkr(proofs[i]);
			data.push_back(encode_gkr_proof(proofs[i]));
			transcript.push_back(get_gkr_transcript(proofs[i]));
		}
	}

	string filename = "proof_input";
	char name[filename.length()+1];
	strcpy(name, filename.c_str());
	string circuit_filename = "proof_transcript";
	char transcript_name[circuit_filename.length()+1];
	strcpy(transcript_name, circuit_filename.c_str());
	write_transcript(transcript,transcript_name);
	//write_proof_data(data,name);

	vector<F> gkr_data;
	for(int i = 0; i < data.size(); i++){
		for(int j = 0; j <data[i].size(); j++){
			gkr_data.push_back(data[i][j]);
		}
	}
	gkr_data.push_back(F(1));
	
	circuit_filename = "verification_circuit.pws";
	char circuit_name[circuit_filename.length()+1];
	strcpy(circuit_name, circuit_filename.c_str());
	vector<F> r(10);
	for(int i = 0; i < 10; i++){
		r[i] = random();//.setByCSPRNG();
	}
	return prove_verification(gkr_data,r,transcript);
	//generate_GKR_proof(circuit_name,name,r,true);
}

int get_transcript_size(vector<proof> proofs){
	vector<vector<F>> data;
	int counter = 0;
	for(int i = 0; i < proofs.size(); i++){
		if(proofs[i].type == MATMUL_PROOF){
			data.push_back(encode_m2m_proof(proofs[i]));
		}else if(proofs[i].type == LOOKUP_PROOF){
			for(int j =  0; j < proofs[i].proofs.size(); j++){
				data.push_back(encode_lookup_proof(proofs[i].proofs[j]));
			}
		}else if(proofs[i].type == HASH_SUMCHECK){
			data.push_back(encode_hash_proof(proofs[i]));
		}
		else if(proofs[i].type == RANGE_PROOF){
			data.push_back(encode_bit_decomposition(proofs[i]));
		}
		else if(proofs[i].type == GKR_PROOF){
			data.push_back(encode_gkr_proof(proofs[i]));
		}
	}
	vector<F> gkr_data;
	for(int i = 0; i < data.size(); i++){
		for(int j = 0; j <data[i].size(); j++){
			counter+=1;
		}
	}
	counter += 1;
	return counter;
}

float verify(vector<proof> proofs){
	clock_t start,end;
	start = clock();
	for(int i = 0; i < proofs.size(); i++){
		if(proofs[i].type == MATMUL_PROOF){
			verify_matrix2matrix(proofs[i]);
		}
		else if(proofs[i].type == RANGE_PROOF || proofs[i].type == RANGE_PROOF_OPT || proofs[i].type == RANGE_PROOF_LOOKUP){
			verify_bit_decomposition(proofs[i]);
		}
		else if(proofs[i].type == GKR_PROOF){
			verify_gkr(proofs[i]);
		}
		else{
			//printf("Proof not found\n");
		}
	}
	end = clock();
	return (float)(end-start)/(float)CLOCKS_PER_SEC;
}


