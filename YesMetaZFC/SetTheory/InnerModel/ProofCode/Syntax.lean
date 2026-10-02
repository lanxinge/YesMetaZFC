import YesMetaZFC.SetTheory.InnerModel.Jensen.Class
import YesMetaZFC.Model.SetTheory.Internal.Numeral
import YesMetaZFC.SetTheory.InnerModel.Order.Coordinates

/-! # 携带序数参数的 J 构造推导码

叶码为 (0,α)，解释为 Jₐ；运算码为 (k+1,(a,(b,c)))。码和推导高度均为
模型内集合；只有固定的十三个运算标签来自宿主有限菜单。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project Internal
universe u
variable {M : Structure.{u}}

def pc_tag_l : Rd_sym → Nat
  | .pair => 1 | .diff => 2 | .prod => 3 | .mid => 4 | .last => 5 | .union => 6
  | .range => 7 | .mem => 8 | .fibers => 9 | .opair => 10 | .triple => 11 | .adj => 12 | .fiber => 13

theorem pc_tag_pos_l (k : Rd_sym) : 0 < pc_tag_l k := by cases k <;> decide

theorem pc_tag_inj_l {k l : Rd_sym} (h : pc_tag_l k = pc_tag_l l) : k = l := by
  cases k <;> cases l <;> simp_all [pc_tag_l]

def pc_num_m : Nat → {n : Nat} → Term n → Formula 1 n
  | 0, _, x => Formula.forallMem x .falsum
  | k+1, _, x => Formula.existsMem x (.conj (pc_num_m k .newest) (KP.succ0_m x.weaken .newest))

@[simp] theorem pc_num_closed_l (k : Nat) {n} (x : Term n) (hx : x.freeSupport = []) :
    (pc_num_m k x).FreeClosed := by
  induction k generalizing n with
  | zero => simp -implicitDefEqProofs [pc_num_m, Definitional.Formula.FreeClosed, hx]
  | succ k ih => simp -implicitDefEqProofs [pc_num_m, Definitional.Formula.FreeClosed, ih, hx]

theorem pc_num_delta_l (k : Nat) {n} (x : Term n) : (pc_num_m k x).IsDelta0 := by
  induction k generalizing n with
  | zero => exact .forallMem _ .falsum
  | succ k ih => exact .existsMem _ (.conj (ih _) (KP.succ0_delta_l ..))

theorem pc_num_sat_l (hE : Extensional M) (k : Nat) {n} (ρ : Env M n) (x : Term n) :
    Formula.satisfies ρ (pc_num_m k x) ↔ Num_d k (x.eval ρ) := by
  induction k generalizing n with
  | zero => simp only [pc_num_m, Num_d, Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff]
  | succ k ih =>
    simp only [pc_num_m, Num_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      ih, KP.succ0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact ⟨fun ⟨a, _, ha, hs⟩ => ⟨a, ha, hs⟩, fun ⟨a, ha, hs⟩ => ⟨a, hs.predecessor_mem, ha, hs⟩⟩

def Pc_leaf_d (T c a : M.Domain) : Prop := ∃ e, M.mem e T ∧ Num_d 0 e ∧ KPair_d M c e a

def pc_leaf_m {n} (T c a : Term n) : Formula 1 n := Formula.existsMem T
  (.conj (pc_num_m 0 .newest) (kpair0_m c.weaken .newest a.weaken))
derive_free_closed pc_leaf_m

theorem pc_leaf_delta_l {n} (T c a : Term n) : (pc_leaf_m T c a).IsDelta0 :=
  .existsMem _ (.conj (pc_num_delta_l ..) (kpair0_delta_l ..))

theorem pc_leaf_sat_l (hE : Extensional M) {n} (ρ : Env M n) (T c a : Term n) :
    Formula.satisfies ρ (pc_leaf_m T c a) ↔ Pc_leaf_d (T.eval ρ) (c.eval ρ) (a.eval ρ) := by
  simp only [pc_leaf_m, Pc_leaf_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    pc_num_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Pc_node_d (T : M.Domain) (k : Rd_sym) (c a b d : M.Domain) : Prop :=
  ∃ t, M.mem t T ∧ ∃ v, M.mem v T ∧ Num_d (pc_tag_l k) t ∧ Rd_triple_d v a b d ∧ KPair_d M c t v

def pc_node_m {n} (T : Term n) (k : Rd_sym) (c a b d : Term n) : Formula 1 n :=
  Formula.existsMem T (Formula.existsMem T.weaken (.conj (pc_num_m (pc_tag_l k) (.bound 1))
    (.conj (rd_triple0_m .newest a.weaken.weaken b.weaken.weaken d.weaken.weaken)
      (kpair0_m c.weaken.weaken (.bound 1) .newest))))
derive_free_closed pc_node_m

theorem pc_node_delta_l {n} (T : Term n) (k : Rd_sym) (c a b d : Term n) : (pc_node_m T k c a b d).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (pc_num_delta_l ..) (.conj (rd_triple0_delta_l ..) (kpair0_delta_l ..))))

theorem pc_node_sat_l (hE : Extensional M) {n} (ρ : Env M n) (T : Term n) (k : Rd_sym) (c a b d : Term n) :
    Formula.satisfies ρ (pc_node_m T k c a b d) ↔ Pc_node_d (T.eval ρ) k (c.eval ρ) (a.eval ρ) (b.eval ρ) (d.eval ρ) := by
  simp only [pc_node_m, Pc_node_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    pc_num_sat_l hE, rd_triple0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem pc_leaf_inj_l {T U c a b : M.Domain} (h : Pc_leaf_d T c a) (g : Pc_leaf_d U c b) : a = b := by
  obtain ⟨_, _, _, hc⟩ := h
  obtain ⟨_, _, _, hd⟩ := g
  exact (kpair_injective_l M hc hd).2

theorem pc_node_inj_l (hKP : M.Models KP) {T U k l c a b d x y z}
    (h : Pc_node_d (M := M) T k c a b d) (g : Pc_node_d U l c x y z) : k = l ∧ a = x ∧ b = y ∧ d = z := by
  obtain ⟨t, _, v, _, ht, hv, hc⟩ := h
  obtain ⟨s, _, w, _, hs, hw, hd⟩ := g
  obtain ⟨he, hf⟩ := kpair_injective_l M hc hd; subst s; subst w
  exact ⟨pc_tag_inj_l (num_injective_l hKP ht hs), pc_triple_inj_l hv hw⟩

theorem pc_leaf_node_false_l (hKP : M.Models KP) {T U c a k x y z}
    (h : Pc_leaf_d (M := M) T c a) (g : Pc_node_d U k c x y z) : False := by
  obtain ⟨e, _, he, hc⟩ := h
  obtain ⟨t, _, v, _, ht, _, hg⟩ := g
  have hh := (kpair_injective_l M hc hg).1; subst t
  have he := num_injective_l hKP he ht
  exact Nat.ne_of_gt (pc_tag_pos_l k) he.symm

theorem pc_leaf_unique_l (hE : Extensional M) {T U c d a : M.Domain}
    (hc : Pc_leaf_d T c a) (hd : Pc_leaf_d U d a) : c = d := by
  obtain ⟨e, _, he, hc⟩ := hc
  obtain ⟨f, _, hf, hd⟩ := hd
  have he := num_unique_l hE he hf; subst f
  exact kpair_unique_l M hE hc hd

theorem pc_node_unique_l (hE : Extensional M) {T U k c d a b e}
    (hc : Pc_node_d (M := M) T k c a b e) (hd : Pc_node_d U k d a b e) : c = d := by
  obtain ⟨t, _, p, _, ht, ⟨q, hq, hp⟩, hc⟩ := hc
  obtain ⟨s, _, r, _, hs, ⟨v, hv, hr⟩, hd⟩ := hd
  have h := num_unique_l hE ht hs; subst s
  have h := kpair_unique_l M hE hq hv; subst v
  have h := kpair_unique_l M hE hp hr; subst r
  exact kpair_unique_l M hE hc hd

def Pc_at_d (F h c x : M.Domain) : Prop := ∃ r, M.mem r F ∧ Rd_triple_d r h c x

def pc_at_m {n} (F h c x : Term n) : Formula 1 n :=
  Formula.existsMem F (rd_triple0_m .newest h.weaken c.weaken x.weaken)
derive_free_closed pc_at_m

theorem pc_at_delta_l {n} (F h c x : Term n) : (pc_at_m F h c x).IsDelta0 := .existsMem _ (rd_triple0_delta_l ..)

theorem pc_at_sat_l (hE : Extensional M) {n} (ρ : Env M n) (F h c x : Term n) :
    Formula.satisfies ρ (pc_at_m F h c x) ↔ Pc_at_d (F.eval ρ) (h.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [pc_at_m, Pc_at_d, Formula.satisfies_existsMem_iff, rd_triple0_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Pc_read_d (F h c x : M.Domain) : Prop := ∃ m, M.mem m h ∧ Pc_at_d F m c x

def pc_read_m {n} (F h c x : Term n) : Formula 1 n :=
  Formula.existsMem h (pc_at_m F.weaken .newest c.weaken x.weaken)
derive_free_closed pc_read_m

theorem pc_read_delta_l {n} (F h c x : Term n) : (pc_read_m F h c x).IsDelta0 := .existsMem _ (pc_at_delta_l ..)

theorem pc_read_sat_l (hE : Extensional M) {n} (ρ : Env M n) (F h c x : Term n) :
    Formula.satisfies ρ (pc_read_m F h c x) ↔ Pc_read_d (F.eval ρ) (h.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [pc_read_m, Pc_read_d, Formula.satisfies_existsMem_iff, pc_at_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

end YesMetaZFC.SetTheory.InnerModel
