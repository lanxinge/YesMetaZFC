import YesMetaZFC.Model.Forcing.Proper.Generic.Elementary
import YesMetaZFC.SetTheory.FinitarySlice

/-! # 以阶段编号索引的共同泛型选择图

阶段编号是内部有限参数列的末项，条件集和关系由两张实际阶段图读取。
名称环境的泛型像由唯一的 Ng_name_d 确定；判定和选择共用同一个解码式。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ng_index_d (ω δ F G X k i B R μ a : M.Domain) : Prop :=
  M.mem i δ ∧ Entry_d M i B F ∧ Entry_d M i R G ∧ Ng_name_d M B X μ ∧
    ∃ l f s, KPair_d M k l s ∧ Fseq_end_d I ω s f i ∧ KPair_d M a l f

def ng_index_m {n} (ω δ F G X k i B R μ a : Term n) : Formula 1 n :=
  .conj (.mem i δ) (.conj (entry_m i B F) (.conj (entry_m i R G) (.conj (ng_name_m B X μ)
    (.existsE (.existsE (.existsE (.conj (kpair_m k.weaken.weaken.weaken (.bound 2) .newest)
      (.conj (fseq_end_m (𝒞 := kpair_convention_l) ω.weaken.weaken.weaken .newest (.bound 1) i.weaken.weaken.weaken)
        (kpair_m a.weaken.weaken.weaken (.bound 2) (.bound 1))))))))))
derive_free_closed ng_index_m

theorem ng_index_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω δ F G X k i B R μ a : Term n) :
    Formula.satisfies ρ (ng_index_m ω δ F G X k i B R μ a) ↔
      Ng_index_d I (ω.eval ρ) (δ.eval ρ) (F.eval ρ) (G.eval ρ) (X.eval ρ) (k.eval ρ)
        (i.eval ρ) (B.eval ρ) (R.eval ρ) (μ.eval ρ) (a.eval ρ) := by
  simp only [ng_index_m, Ng_index_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    entry_sat_l M hE, ng_name_sat_l M hE, Formula.satisfies_exists_iff, kpair_sat_l M hE,
    fseq_end_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem ng_index_unique_l (hE : Extensional M) {ω δ F G X k i B R μ a j C S ν d}
    (hF : ∀ i B C, Entry_d M i B F → Entry_d M i C F → B = C)
    (hG : ∀ i R S, Entry_d M i R G → Entry_d M i S G → R = S)
    (h : Ng_index_d I ω δ F G X k i B R μ a) (h' : Ng_index_d I ω δ F G X k j C S ν d) :
    i = j ∧ B = C ∧ R = S ∧ μ = ν ∧ a = d := by
  obtain ⟨hi, hiB, hiR, hμ, l, f, s, hk, hs, ha⟩ := h
  obtain ⟨hj, hjC, hjS, hν, l', f', s', hk', hs', hd⟩ := h'
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hk hk'
  obtain ⟨rfl, rfl⟩ := fseq_end_unique_l I hE hs hs'
  have hBC := hF i B C hiB hjC
  have hRS := hG i R S hiR hjS
  subst C S
  exact ⟨rfl, rfl, rfl, ng_name_unique_l M hE hμ hν, kpair_unique_l M hE ha hd⟩

def Ng_index_op_d (k : Bool) (B R b ω X w μ u a t : M.Domain) : Prop :=
  if k then Ng_select_op_d I (ssk_mem_s kpair_convention_l) (ng_elementary_env_l w μ u) B R B b ω X u a t
  else Ng_dense_op_d (ssk_mem_s kpair_convention_l) (ng_elementary_env_l w μ u) B R B b X a t

def ng_index_op_m {n} (k : Bool) (B R b ω X w μ u a t : Term n) : Formula 1 n :=
  let e : Fin 3 → Term n := Fin.cases u (Fin.cases μ (fun _ => w))
  if k then ng_select_op_m (ssk_mem_s kpair_convention_l) e B R B b ω X u a t
  else ng_dense_op_m (ssk_mem_s kpair_convention_l) e B R B b X a t

@[simp] theorem ng_index_op_closed_l {n} (k : Bool) (B R b ω X w μ u a t : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hb : b.freeSupport = [])
    (hω : ω.freeSupport = []) (hX : X.freeSupport = []) (hw : w.freeSupport = [])
    (hμ : μ.freeSupport = []) (hu : u.freeSupport = []) (ha : a.freeSupport = []) (ht : t.freeSupport = []) :
    (ng_index_op_m k B R b ω X w μ u a t).FreeClosed := by
  have he : ∀ i : Fin 3, (Fin.cases u (Fin.cases μ (fun _ => w)) i : Term n).freeSupport = [] :=
    Fin.cases hu (Fin.cases hμ (fun _ => hw))
  cases k <;> simp -implicitDefEqProofs [ng_index_op_m, *]

theorem ng_index_op_sat_l (hE : Extensional M) {n} (k : Bool) (ρ : Env M n)
    (B R b ω X w μ u a t : Term n) :
    Formula.satisfies ρ (ng_index_op_m k B R b ω X w μ u a t) ↔
      Ng_index_op_d I k (B.eval ρ) (R.eval ρ) (b.eval ρ) (ω.eval ρ) (X.eval ρ)
        (w.eval ρ) (μ.eval ρ) (u.eval ρ) (a.eval ρ) (t.eval ρ) := by
  cases k
  · exact (ng_dense_op_sat_l hE _ ρ _ _ _ _ _ _ _ _).trans
      (ng_dense_env_l hE _ _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) _ _ _ _ _ _ _)
  · exact (ng_select_op_sat_l I hE _ ρ _ _ _ _ _ _ _ _ _ _).trans
      (ng_select_env_l I hE _ _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) _ _ _ _ _ _ _ _ _)

def Ng_joint_d (k : Bool) (ω δ F G b X w u p t : M.Domain) : Prop :=
  (∃ i B R μ a, Ng_index_d I ω δ F G X p i B R μ a ∧ Ng_index_op_d I k B R b ω X w μ u a t) ∨
    ((¬ ∃ i B R μ a, Ng_index_d I ω δ F G X p i B R μ a) ∧ t = u)

def ng_index_exists_m {n} (ω δ F G X p : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE
    (ng_index_m ω.weaken.weaken.weaken.weaken.weaken δ.weaken.weaken.weaken.weaken.weaken
      F.weaken.weaken.weaken.weaken.weaken G.weaken.weaken.weaken.weaken.weaken
      X.weaken.weaken.weaken.weaken.weaken p.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)))))
derive_free_closed ng_index_exists_m

def ng_joint_m {n} (k : Bool) (ω δ F G b X w u p t : Term n) : Formula 1 n :=
  .disj (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ng_index_m ω.weaken.weaken.weaken.weaken.weaken δ.weaken.weaken.weaken.weaken.weaken
      F.weaken.weaken.weaken.weaken.weaken G.weaken.weaken.weaken.weaken.weaken
      X.weaken.weaken.weaken.weaken.weaken p.weaken.weaken.weaken.weaken.weaken
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
    (ng_index_op_m k (.bound 3) (.bound 2) b.weaken.weaken.weaken.weaken.weaken
      ω.weaken.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken.weaken
      w.weaken.weaken.weaken.weaken.weaken (.bound 1) u.weaken.weaken.weaken.weaken.weaken
      .newest t.weaken.weaken.weaken.weaken.weaken)))))))
    (.conj (.neg (ng_index_exists_m ω δ F G X p)) (Formula.extensionalEq t u))

@[simp] theorem ng_joint_closed_l {n} (k : Bool) (ω δ F G b X w u p t : Term n)
    (hω : ω.freeSupport = []) (hδ : δ.freeSupport = []) (hF : F.freeSupport = []) (hG : G.freeSupport = [])
    (hb : b.freeSupport = []) (hX : X.freeSupport = []) (hw : w.freeSupport = [])
    (hu : u.freeSupport = []) (hp : p.freeSupport = []) (ht : t.freeSupport = []) :
    (ng_joint_m k ω δ F G b X w u p t).FreeClosed := by
  simp -implicitDefEqProofs [ng_joint_m, Definitional.Formula.FreeClosed, *]

theorem ng_joint_sat_l (hE : Extensional M) {n} (k : Bool) (ρ : Env M n)
    (ω δ F G b X w u p t : Term n) :
    Formula.satisfies ρ (ng_joint_m k ω δ F G b X w u p t) ↔
      Ng_joint_d I k (ω.eval ρ) (δ.eval ρ) (F.eval ρ) (G.eval ρ) (b.eval ρ) (X.eval ρ)
        (w.eval ρ) (u.eval ρ) (p.eval ρ) (t.eval ρ) := by
  simp only [ng_joint_m, ng_index_exists_m, Ng_joint_d, Formula.satisfies_disj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, ng_index_sat_l I hE, ng_index_op_sat_l I hE,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
