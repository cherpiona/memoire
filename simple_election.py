import json
import hashlib
import canonicaljson
import elgamal
from random import randint
from vote_dproof import verify_ballot, generate_ballot

def _hashg(json_obj, q):
    """Hash a JSON object to a integer modulo q.

    :param json_obj: JSON object encoded into a str.

    Procedure:
    * map the object to json in binary canonical form (see
    <https://pypi.org/project/canonicaljson/>)
    * hash it with SHA256
    * interpret the byte string as a big-endian integer
    * reduce it mod q
    """
    return int.from_bytes(
            hashlib.sha256(canonicaljson.dumps(json.loads(json_obj))).digest(),
            byteorder='big'
            ) % q


"""
    ELECTION INITIALIZATION
"""
def combine_keys(G, partial_keys):
    """
    Given the partial keys of the trustees, combine them to obtain the key of the election.
    """
    # QUESTION 5.1
    #assert [key[1].G == G for key in partial_keys]    
    #assert [key[1] == key[0].pk() for key in partial_keys]
    assert [key.G == G for key in partial_keys]   

    pk = 1 # TO COMPLETE
    
    for key in partial_keys:
        pk=pk*key.y

    return elgamal.ElgamalPublicKey(G, pk)

def prove_key_correctness(elgamal_key):
    """
    Given an elgamal key, return a valid proof of knowledge of the secret key.
    To do so, use the _hashg method.
    """
    # QUESTION 5.3
    pk = elgamal_key.pk().y
    group=elgamal_key.G
    sk,commit = elgamal.gen_elgamal_keypair(group)
    challenge=_hashg(json.dumps({
                "commit": commit,
                "pk": pk,
                }), group.q)
    response = sk+challenge*elgamal_key.x %group.q # TO COMPLETE

    return {"pk": pk,
            "commit": commit,
            "response": response}
###j'ai du modifier pour ajouter G
def validate_key_correctness(key,group):
    """
    Given a proof of knowledge of the secret key of an elgamal key,
    verify that the proof is correct.
    """
    # QUESTION 5.2
    pk = key["pk"] 
    commit = key["commit"] 
    response = key["response"]
    group=elgamal.ElGamalGroup(group["p"],group["g"])
    challenge=_hashg(json.dumps({
                "commit": commit,
                "pk": pk,
                }), group.q)
    if pow(group.g,response,group.p)==commit*pow(pk,challenge,group.p)%group.p:
        return True
    # Verify the proof

    return False

def generate_empty_bb(p, g, pk):
    return {"group": {"p": p, "g": g}, "pk": pk, "ballots": []}

def generate_election(n_trustees, p = None, g = None):
    if p == None or g == None:
        G = elgamal.gen_group()
        p = G.p
        g = G.g
    else:
        G = elgamal.ElGamalGroup(p, g)
    partial_keys = [elgamal.gen_elgamal_keypair(G) for i in range(n_trustees)]
   
    pk = combine_keys(G, partial_keys)
    
    bb = generate_empty_bb(p, g, pk.y)
    
    #bb["tallier_keys"] = [prove_key_correctness(key) for key in partial_keys]
    return bb, partial_keys

"""
    VOTING PHASE
"""

def cast_vote(bb, vote):
    """
    Given the bulletin board bb of an election and a 0-1 vote, update 
    the bulletin board with a valid ballot of the vote.
    """
    # QUESTION 4.3
    assert vote in (0, 1)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    public_key=elgamal.ElgamalPublicKey(group,bb["group"]["pk"])
    ballot = generate_ballot(public_key, vote)
    bb["ballots"].append(ballot)

"""
    COMPUTATION OF THE DECRYPTION FACTORS  
"""

def compute_tally_encryption(bb):
    """ 
    Given the bulletin board bb of an election, return a valid encryption
    of the result of the election.
    """
    # QUESTION 4.1
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    
    #pk=combine_keys(group,bb["tallier_keys"])
    public_key=elgamal.ElgamalPublicKey(group,bb["pk"])
    blank_ballot=public_key.encrypt(0)
    encrypted_tally=blank_ballot
    for ballots in bb["ballots"]:
        ###verifier preuve avant
        ballot=elgamal.ElgamalCiphertext(group,ballots["ct"]["c1"],ballots["ct"]["c2"])
        assert[verify_ballot(public_key,ballots)]
        encrypted_tally.homomorphic_add(ballot)
    return encrypted_tally

def compute_decryption_factor_without_proof(tally_encryption, partial_key):
    """
    Given an encryption of the tally and the partial key of a trustee,
    compute the corresponding decryption factor.
    """
    # QUESTION 5.1

    df = pow(tally_encryption.c1,partial_key.x,partial_key.G.p) % partial_key.G.p
    

    return df


def compute_decryption_factor_with_proof(tally_encryption, partial_key):
    """
    Given an encryption of the tally and the partial key of a trustee,
    compute the corresponding decryption factor and the corresponding proof of 
    correct computation.
    To do so, use the _hashg method.
    """
    # QUESTION 5.3    

    pk = partial_key.pk
    c1 = tally_encryption.c1
    group=tally_encryption.G
    df = compute_decryption_factor_without_proof(tally_encryption,partial_key) 
    s=randint(0, group.q-1)
    commit = [pow(group.g,s,group.p),pow(c1,s,group.p)]
    challenge=_hashg(json.dumps({
                    " pk ": pk,
                    " c1 ": c1,
                    " decryption_factor ": df ,
                    " commit ": commit 
                    }), group.q)
    response = s+challenge*partial_key.sk% group.q
    
    return {"pk": pk,
            "c1": c1,
            "decryption_factor": df,
            "commit": commit,
            "response": response
            }

def validate_decryption_factor_proof(decryption_factor,group):
    """
    Given a proof of correctness of a decryption factor,
    verify that the proof is correct.
    """
    # QUESTION 5.2

    pk = decryption_factor["pk"]
    c1 = decryption_factor["c1"]
    df = decryption_factor["decryption_factor"]
    commit = decryption_factor["commit"]
    response = decryption_factor["response"]
    
    challenge=_hashg(json.dumps({
                " pk ": pk,
                " c1 ": c1,
                " decryption_factor ": df ,
                " commit ": commit 
                }), group.q)
    # Verify the proof
    if pow(group.g,response,group.p)== commit[0]*pow(pk,challenge,group.p) and pow(c1,response,group.p)== commit[1]*pow(df,challenge,group.p)%group.p:
        return True
    

    
    return False


def compute_all_decryption_factors(bb, partial_keys):
    tally_encryption = compute_tally_encryption(bb)
    decryption_factors = [compute_decryption_factor_with_proof(tally_encryption, key)
                            for key in partial_keys]
    
    bb["decryption_factors"] = decryption_factors 

"""
    COMPUTE THE FINAL RESULT OF THE ELECTION
"""

def combine_decryption_factors(bb):
    """
    Given the bulletin board bb of an election with the decryption factors,
    comptue the final result.
    """
    # QUESTION 5.2
    ##verifier

    ##encrypted_tally=compute_tally_encryption(bb) faux
    #compute public key
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    partial_key=[]
    for i in bb["tallier_keys"]:
        partial_key.append(elgamal.ElgamalPublicKey(group,i["pk"]))

    pk=combine_keys(group,partial_key)
    #compute encrypted tally
    blank_ballot=pk.encrypt(0)
    encrypted_tally=blank_ballot
    for ballots in bb["ballots"]:
        ###verifier preuve avant
        ballot=elgamal.ElgamalCiphertext(group,ballots["ct"]["c1"],ballots["ct"]["c2"])
        assert[verify_ballot(pk,ballots)]
        encrypted_tally.homomorphic_add(ballot)
        
    #fusion partiel decryption 
    df=pow(group.g,group.q,group.p)
    for dfpartiel in bb["decryption_factors"]:
        validate_decryption_factor_proof(dfpartiel,group)
        df=df*dfpartiel["decryption_factor"] % group.p
        
    res = encrypted_tally.c2/df
    return res

def tally(bb):
    """
    Given the bulletin board bb of an election with the decryption factors,
    validate the correctness of the bulletin board and compute the final result.
    Return None if one of the trustees has cheated.
    """
    # QUESTION 5.2
    
    # Verify the proofs and compute the result
    g_m=combine_decryption_factors(bb)
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    m = elgamal.dLog(group.p, group.g, g_m)
    for df in bb["decryption_factors"]:     
        if validate_decryption_factor_proof(df,group)==False:
            return None
    return m

# QUESTION 4.1: Read the bulletin board and compute an encryption of the tally. 
#               Ask the decryption oracle for the result of the election.
# QUESTION 4.2: What is the vote of the first ballot? 

#test



with open("bb_test.json", "r") as fd:
    bb = json.loads(fd.readline())
    #test
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    sk=elgamal.ElgamalSecretKey(group,567904)
    pk=sk.pk()
    
    cipher=pk.encrypt(18)
    test=sk.decrypt(cipher)

    pk2=elgamal.ElgamalPublicKey(group,bb["pk"])
    cipher2=pk2.encrypt(18)
    test2=sk.decrypt(cipher2)

    ###########compute the encrypted tally
    resultat=compute_tally_encryption(bb)
    #decrypt
    group=elgamal.ElgamalGroup(bb["group"]["p"],bb["group"]["g"])
    sk=elgamal.ElgamalSecretKey(group,567904)
    m=sk.decrypt(resultat)

    #decrypt first ballot

    vote_1=elgamal.ElgamalCiphertext(group,bb["ballots"][0]["ct"]["c1"],bb["ballots"][0]["ct"]["c2"])
    m1=sk.decrypt(resultat)

    
      


# QUESTION 5.2: Read the bulletin board with the decryption factors and verify 
#               the result of the election.
with open("bb_proof.json", "r") as fd:
    bb = json.loads(fd.readline())
    m=tally(bb)
    print(m)

