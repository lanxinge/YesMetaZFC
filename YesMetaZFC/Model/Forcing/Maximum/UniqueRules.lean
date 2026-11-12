import YesMetaZFC.Model.Forcing.Names.Realization
import YesMetaZFC.Model.Forcing.Truth.OrderCongruence

/-! # 输入名称的唯一最小闭名称库

对所有包含给定两名称的闭支撑取交：先用任一共同闭支撑给出集合界，再按
实际原公式分离。所得最小库与最初见证无关，可用于确定的后继递归装配。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

structure Name_hull_d (B s t W : M.Domain) : Prop where
  left : M.mem s W
  right : M.mem t W
  closed : Supp_d M B W
  least : ∀ S, M.mem s S → M.mem t S → Supp_d M B S → M.MemberSubset W S

def name_hull_m {n} (B s t W : Term n) : Formula 1 n :=
  .conj (.mem s W) (.conj (.mem t W) (.conj (supp_m B W)
    (.forallE (.imp (.mem s.weaken .newest) (.imp (.mem t.weaken .newest)
      (.imp (supp_m B.weaken .newest) (Formula.subset W.weaken .newest)))))))
derive_free_closed name_hull_m

theorem name_hull_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B s t W : Term n) :
    Formula.satisfies ρ (name_hull_m B s t W) ↔
      Name_hull_d M (B.eval ρ) (s.eval ρ) (t.eval ρ) (W.eval ρ) := by
  simp only [name_hull_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    supp_sat_l M hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.left, h.right, h.closed, h.least⟩⟩

/-- 最小闭库在原 ZF 内存在；没有选定泛型，也不沿外部良基关系递归。 -/
theorem name_hull_exists_l (hZF : M.Models ZF) {B s t} (hs : Name_d M B s) (ht : Name_d M B t) :
    ∃ W, Name_hull_d M B s t W := by
  obtain ⟨S, hsS, htS, hS⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hs ht
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push s).push t
  let φ : UnarySchema 3 := {
    body := .forallE (.imp (.mem (.bound 3) .newest) (.imp (.mem (.bound 2) .newest)
      (.imp (supp_m (.bound 4) .newest) (.mem (.bound 1) .newest)))) }
  have hφ x : φ.denote ρ x ↔ ∀ U, M.mem s U → M.mem t U → Supp_d M B U → M.mem x U := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, supp_sat_l M hZF.1]
    rfl
  obtain ⟨W, hW'⟩ := ZF.separation_exists_d hZF φ ρ S
  have hW x : M.mem x W ↔ ∀ U, M.mem s U → M.mem t U → Supp_d M B U → M.mem x U := by
    refine (hW' x).trans ?_
    change (M.mem x S ∧ φ.denote ρ x) ↔ _
    rw [hφ x]
    exact ⟨And.right, fun hx => ⟨hx S hsS htS hS, hx⟩⟩
  refine ⟨W, ⟨(hW s).mpr (fun _ hs _ _ => hs), (hW t).mpr (fun _ _ ht _ => ht), ?_, ?_⟩⟩
  · intro x hx v hv
    obtain ⟨a, b, hab, _, hb⟩ := hS x ((hW x).mp hx S hsS htS hS) v hv
    exact ⟨a, b, hab, (hW a).mpr (fun U hsU htU hU =>
      (supp_entry_l M hU ((hW x).mp hx U hsU htU hU) ⟨v, hab, hv⟩).1), hb⟩
  · exact fun U hsU htU hU x hx => (hW x).mp hx U hsU htU hU

theorem name_hull_unique_l (hE : Extensional M) {B s t W W'}
    (h : Name_hull_d M B s t W) (h' : Name_hull_d M B s t W') : W = W' :=
  hE.eq_of_same_members W W' (fun x =>
    ⟨h.least W' h'.left h'.right h'.closed x, h'.least W h.left h.right h.closed x⟩)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 任意内部预序上的名称混合

由实际公式选择的名称族可以沿条件拼合。重叠选择只需在共同加强上被迫使相等；
混合结论同样是局部等号力迫，不依赖某个已经选定的泛型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

/-- 在条件交叠处相容的可定义名称选择具有实际混合名称。 -/
theorem mixing_l {n} (φ : BinarySchema n) (ρ : Env M n) {W} (hW : Supp_d M B W)
    (hc : ∀ p q s t r, M.mem p B → M.mem q B → M.mem s W → M.mem t W →
      φ.denote ρ s p → φ.denote ρ t q → Below_d M B R z r p → Below_d M B R z r q →
      Eq_force_d M B R z r s t) :
    ∃ u, Name_d M B u ∧
      (∀ a d, Entry_d M a d u → ∃ s b, M.mem s W ∧ Entry_d M a b s) ∧
      ∀ p s, M.mem p B → M.mem s W → φ.denote ρ s p → Eq_force_d M B R z p u s := by
  let δ := (((ρ.push B).push R).push z).push W
  let e : Fin n → Term (n+9) := fun i => .bound ⟨i.val+9, by omega⟩
  let ψ : BinarySchema (n+4) := {
    body := .existsE (.existsE (.existsE
      (.conj (.mem (.bound 2) (.bound 5)) (.conj (.mem (.bound 1) (.bound 8))
        (.conj (binary_pred_m φ e (.bound 2) (.bound 1))
          (.conj (below_m (.bound 8) (.bound 7) (.bound 6) (.bound 3) (.bound 1))
            (.conj (entry_m (.bound 4) .newest (.bound 2)) (entry_m (.bound 3) .newest (.bound 7)))))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, e] }
  have hψ a d : ψ.denote δ a d ↔ ∃ t p b,
      M.mem t W ∧ M.mem p B ∧ φ.denote ρ t p ∧ Below_d M B R z d p ∧
        Entry_d M a b t ∧ Entry_d M d b R := by
    have he t p b : (⟨fun i => (e i).eval (((((δ.push a).push d).push t).push p).push b),
        (((((δ.push a).push d).push t).push p).push b).free⟩ : Env M n) = ρ := by cases ρ; rfl
    simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, binary_pred_sat_l, below_sat_l M hZF.1, entry_sat_l M hZF.1, he]
    rfl
  obtain ⟨u, hu, _, hU⟩ := name_comp_l M hZF ψ δ B W (fun a ha => ⟨W, ha, hW⟩)
  have bound a d (had : Entry_d M a d u) : ∃ s b, M.mem s W ∧ Entry_d M a b s := by
    obtain ⟨s, _, b, hs, _, _, _, hab, _⟩ := (hψ a d).mp ((hU a d).mp had).2.2
    exact ⟨s, b, hs, hab⟩
  refine ⟨u, hu, bound, fun p t hp ht hφ => ?_⟩
  have htN : Name_d M B t := ⟨W, ht, hW⟩
  apply (eq_force_unfold_l M hZF hu htN).mpr
  refine ⟨hp, ?_, ?_⟩
  · intro a d had q hq hqd
    obtain ⟨_, hdB, hψ'⟩ := (hU a d).mp had
    obtain ⟨s, r, b, hs, hrB, hsr, hdr, hab, hdb⟩ := (hψ a d).mp hψ'
    have hbB := (supp_entry_l M hW hs hab).2
    have hqr := below_trans_l O hrB ⟨hq.1, hq.2.1, hqd⟩ hdr
    have hqb := O.trans q d b hq.1 hdB hbB hqd hdb
    have he := hc r p s t q hrB hp hs ht hsr hφ hqr hq
    have hl := (eq_force_unfold_l M hZF ⟨W, hs, hW⟩ htN).mp he |>.2.1
    exact hl a b hab q (below_refl_l O hq.1 hq.2.1) hqb
  · intro a b hab q hq hqb
    have ha := (supp_entry_l M hW ht hab).1
    refine ⟨q, a, q, below_refl_l O hq.1 hq.2.1, ?_, O.refl q hq.1,
      eq_force_refl_l O hZF hq.1 ⟨W, ha, hW⟩⟩
    exact (hU a q).mpr ⟨ha, hq.1, (hψ a q).mpr ⟨t, p, b, ht, hp, hφ, hq, hab, hqb⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 混合闭合的确定名称库

令 S 为输入名称的最小闭支撑，取 W = 𝒫(S × B)。闭性给出 S ⊆ W；
W 中名称的子名称仍在 S，故任意可定义混合仍在 W。整个构造只使用原 ZF，
幂集、乘积和所有量词都在地模型内部，不要求外部良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

/-- 名称的所有直接条目位于 S × B。 -/
def Name_bound_d (B S t : M.Domain) : Prop :=
  ∀ v, M.mem v t → ∃ a b, KPair_d M v a b ∧ M.mem a S ∧ M.mem b B

def name_bound_m {n} (B S t : Term n) : Formula 1 n :=
  Formula.forallMem t (.existsE (.existsE
    (.conj (kpair_m (.bound 2) (.bound 1) .newest)
      (.conj (.mem (.bound 1) S.weaken.weaken.weaken) (.mem .newest B.weaken.weaken.weaken)))))
derive_free_closed name_bound_m

theorem name_bound_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B S t : Term n) :
    Formula.satisfies ρ (name_bound_m B S t) ↔
      Name_bound_d M (B.eval ρ) (S.eval ρ) (t.eval ρ) := by
  simp only [name_bound_m, Name_bound_d, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    kpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Name_pool_d (B s t W : M.Domain) : Prop :=
  ∃ S, Name_hull_d M B s t S ∧ ∀ a, M.mem a W ↔ Name_bound_d M B S a

def name_pool_m {n} (B s t W : Term n) : Formula 1 n :=
  .existsE (.conj (name_hull_m B.weaken s.weaken t.weaken .newest)
    (.forallE (.iff (.mem .newest W.weaken.weaken)
      (name_bound_m B.weaken.weaken (.bound 1) .newest))))
derive_free_closed name_pool_m

theorem name_pool_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B s t W : Term n) :
    Formula.satisfies ρ (name_pool_m B s t W) ↔
      Name_pool_d M (B.eval ρ) (s.eval ρ) (t.eval ρ) (W.eval ρ) := by
  simp only [name_pool_m, Name_pool_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    name_hull_sat_l M hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, name_bound_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem name_pool_exists_l (hZF : M.Models ZF) {B s t}
    (hs : Name_d M B s) (ht : Name_d M B t) : ∃ W, Name_pool_d M B s t W := by
  obtain ⟨S, hS⟩ := name_hull_exists_l M hZF hs ht
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF X
  refine ⟨W, S, hS, fun a => (hW a).trans ?_⟩
  exact ⟨fun h v hv => by
    obtain ⟨s, hs, b, hb, hp⟩ := (hX v).mp (h v hv)
    exact ⟨s, b, hp, hs, hb⟩, fun h v hv => by
    obtain ⟨s, b, hp, hs, hb⟩ := h v hv
    exact (hX v).mpr ⟨s, hs, b, hb, hp⟩⟩

theorem name_pool_unique_l (hE : Extensional M) {B s t W V}
    (h : Name_pool_d M B s t W) (k : Name_pool_d M B s t V) : W = V := by
  obtain ⟨S, hS, hW⟩ := h
  obtain ⟨T, hT, hV⟩ := k
  have he := name_hull_unique_l M hE hS hT
  subst T
  exact hE.eq_of_same_members W V (fun a => (hW a).trans (hV a).symm)

variable {M} {B s t W : M.Domain}

theorem Name_pool_d.left (h : Name_pool_d M B s t W) : M.mem s W := by
  obtain ⟨S, hS, hW⟩ := h
  exact (hW s).mpr (hS.closed s hS.left)

theorem Name_pool_d.right (h : Name_pool_d M B s t W) : M.mem t W := by
  obtain ⟨S, hS, hW⟩ := h
  exact (hW t).mpr (hS.closed t hS.right)

theorem Name_pool_d.closed (h : Name_pool_d M B s t W) : Supp_d M B W := by
  obtain ⟨S, hS, hW⟩ := h
  intro a ha v hv
  obtain ⟨c, b, hc, hcS, hb⟩ := (hW a).mp ha v hv
  exact ⟨c, b, hc, (hW c).mpr (hS.closed c hcS), hb⟩

/-- 任意名称只要其直接子名称来自库中名称的直接子名称，就仍在同一库中。 -/
theorem Name_pool_d.mem_of_entries (h : Name_pool_d M B s t W) {q}
    (hq : Name_d M B q)
    (hb : ∀ a d, Entry_d M a d q → ∃ r b, M.mem r W ∧ Entry_d M a b r) : M.mem q W := by
  obtain ⟨S, hS, hW⟩ := h
  apply (hW q).mpr
  obtain ⟨V, hqV, hV⟩ := hq
  intro v hv
  obtain ⟨a, d, hvad, _, hd⟩ := hV q hqV v hv
  obtain ⟨r, b, hr, w, hwa, hw⟩ := hb a d ⟨v, hvad, hv⟩
  obtain ⟨a', b', hw', ha, _⟩ := (hW r).mp hr w hw
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hwa hw'
  exact ⟨a, d, hvad, ha, hd⟩

/-- 给定实际公式的相容选择族，其混合名称不离开已装配的名称库。 -/
theorem name_pool_mix_l {R z} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Name_pool_d M B s t W) {n} (φ : BinarySchema n) (ρ : Env M n)
    (hc : ∀ p q a b r, M.mem p B → M.mem q B → M.mem a W → M.mem b W →
      φ.denote ρ a p → φ.denote ρ b q → Below_d M B R z r p → Below_d M B R z r q →
      Eq_force_d M B R z r a b) :
    ∃ a, M.mem a W ∧ ∀ p b, M.mem p B → M.mem b W → φ.denote ρ b p → Eq_force_d M B R z p a b := by
  obtain ⟨a, ha, hb, hm⟩ := mixing_l O hZF φ ρ h.closed hc
  exact ⟨a, h.mem_of_entries ha hb, hm⟩

/-- 被迫属于目标集的任意名称，在同一条件上有库内等值代表；只需 ZF。 -/
theorem name_pool_represent_l {R z v} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Name_pool_d M B s t W) (hv : Name_d M B v) :
    ∃ a, M.mem a W ∧ ∀ p, Mem_force_d M B R z p v s → Eq_force_d M B R z p a v := by
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push v
  let φ : BinarySchema 4 := {
    body := eq_force_m (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1) (.bound 2) }
  have hφ a p : φ.denote ρ a p ↔ Eq_force_d M B R z p a v :=
    eq_force_sat_l M hZF.1 ((ρ.push a).push p) _ _ _ _ _ _
  have hn a (ha : M.mem a W) : Name_d M B a := ⟨W, ha, h.closed⟩
  obtain ⟨a, ha, hm⟩ := name_pool_mix_l O hZF h φ ρ (by
    intro p q a b r hp hq ha hb hpa hqb hrp hrq
    exact eq_force_trans_l O hZF (hn a ha) hv (hn b hb)
      (eq_force_lower_l O hZF (hn a ha) hv p r hp hrp ((hφ a p).mp hpa))
      (eq_force_symm_l hZF (hn b hb) hv
        (eq_force_lower_l O hZF (hn b hb) hv q r hq hrq ((hφ b q).mp hqb))))
  refine ⟨a, ha, fun p hp => eq_force_dense_l O hZF (hn a ha) hv hp.1 ?_⟩
  intro q hq
  obtain ⟨r, b, c, hr, hbc, _, he⟩ := hp.2 q hq
  have hb := (supp_entry_l M h.closed h.left hbc).1
  have he' := eq_force_symm_l hZF hv (hn b hb) he
  exact ⟨r, hr, eq_force_trans_l O hZF (hn a ha) (hn b hb) hv
    (hm r b hr.1 hb ((hφ b r).mpr he')) he'⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 在固定名称库内修补局部见证

若 s 只在部分条件下满足 φ，则在这些条件上保留 s，在迫使 ¬φ(s) 的条件上
使用已有的全局见证 t。两类条件不能相容，故实际混合仍属于同一名称库。
这使稠密集的局部名称变成全局稠密集名称，而不改变它在给定泛型中的值。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {B R z s t W : M.Domain}

theorem name_pool_patch_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {n} (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i))
    {v w} (pool : Name_pool_d M B v w W) (hs : M.mem s W) (ht : M.mem t W)
    (fallback : ∀ p, M.mem p B → p ≠ z → Forces_d M B R z φ.body (ρ.push t) p) :
    ∃ a, M.mem a W ∧
      (∀ p, M.mem p B → p ≠ z → Forces_d M B R z φ.body (ρ.push a) p) ∧
      ∀ p, M.mem p B → Forces_d M B R z φ.body (ρ.push s) p → Eq_force_d M B R z p a s := by
  classical
  have hn x (hx : M.mem x W) : Name_d M B x := ⟨W, hx, pool.closed⟩
  let η : Env M n := ⟨ρ.bound, fun _ => s⟩
  have change_env x p := forces_env_l (B := B) (R := R) (z := z) hZF.1
    φ.body φ.freeClosed (ρ.push x) (η.push x) (fun _ => rfl) p
  have reg x (hx : M.mem x W) := forces_regular_l O hZF φ.body (η.push x) (by
    intro a
    cases a with
    | free _ => exact hn s hs
    | bound i => exact Fin.cases (hn x hx) hρ i)
  let δ := ((((η.push B).push R).push z).push s).push t
  let es : Fin (n+1) → Term (n+7) := Fin.cases (.bound 3) (fun i => .bound ⟨i.val+7, by omega⟩)
  let χ : BinarySchema (n+5) := {
    body := .disj
      (.conj (Formula.extensionalEq (.bound 1) (.bound 3))
        (force_at_m φ.body es (.bound 6) (.bound 5) (.bound 4) .newest))
      (.conj (Formula.extensionalEq (.bound 1) (.bound 2))
        (force_at_m (.neg φ.body) es (.bound 6) (.bound 5) (.bound 4) .newest))
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed]
      refine ⟨⟨by simp -implicitDefEqProofs, ?_⟩, by simp -implicitDefEqProofs, ?_⟩
      · exact force_at_closed_l _ _ _ _ _ _ φ.freeClosed (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl
      · exact force_at_closed_l _ _ _ _ _ _ φ.freeClosed (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl }
  have hχ a p : χ.denote δ a p ↔
      (a = s ∧ Forces_d M B R z φ.body (η.push s) p) ∨
      (a = t ∧ Forces_d M B R z (.neg φ.body) (η.push s) p) := by
    have he : (⟨fun i => (es i).eval ((δ.push a).push p), ((δ.push a).push p).free⟩ : Env M (n+1)) = η.push s := by
      apply congrArg (fun f => (⟨f, fun _ => s⟩ : Env M (n+1)))
      exact funext (Fin.cases rfl (fun _ => rfl))
    simp only [BinarySchema.denote, χ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, force_at_sat_l, he]
    rfl
  have clash p q r (hp : M.mem p B) (hrp : Below_d M B R z r p) (hrq : Below_d M B R z r q)
      (yes : Forces_d M B R z φ.body (η.push s) p)
      (no : Forces_d M B R z (.neg φ.body) (η.push s) q) : False :=
    (forces_neg_l hZF.1 _ _ q).mp no r hrq ((reg s hs).1 p r hp hrp yes)
  obtain ⟨a, ha, mix⟩ := name_pool_mix_l O hZF pool χ δ (by
    intro p q a b r hp hq _ _ hpa hqb hrp hrq
    rcases (hχ a p).mp hpa with ⟨ha, yes⟩ | ⟨ha, no⟩
    · rcases (hχ b q).mp hqb with ⟨hb, _⟩ | ⟨_, no⟩
      · rw [ha, hb]; exact eq_force_refl_l O hZF hrp.1 (hn s hs)
      · exact (clash p q r hp hrp hrq yes no).elim
    · rcases (hχ b q).mp hqb with ⟨_, yes⟩ | ⟨hb, _⟩
      · exact (clash q p r hq hrq hrp yes no).elim
      · rw [ha, hb]; exact eq_force_refl_l O hZF hrp.1 (hn t ht))
  have same p hp hf : Eq_force_d M B R z p a s := mix p s hp hs ((hχ s p).mpr (Or.inl ⟨rfl, hf⟩))
  refine ⟨a, ha, ?_, fun p hp hf => same p hp ((change_env s p).mp hf)⟩
  intro p hp hz
  apply (change_env a p).mpr
  apply (reg a ha).2 p hp hz
  intro q hq
  by_cases yes : Forces_d M B R z φ.body (η.push s) q
  · exact ⟨q, below_refl_l O hq.1 hq.2.1,
      (forces_name_congr_l O hZF φ η hρ (hn a ha) (hn s hs) hq.1 hq.2.1 (same q hq.1 yes)).mpr yes⟩
  · obtain ⟨r, hr, no⟩ := regular_neg_witness_l (reg s hs) hq.1 hq.2.1 yes
    have eq := mix r t hr.1 ht ((hχ t r).mpr (Or.inr ⟨rfl, (forces_neg_l hZF.1 _ _ r).mpr no⟩))
    exact ⟨r, hr, (forces_name_congr_l O hZF φ η hρ (hn a ha) (hn t ht) hr.1 hr.2.1 eq).mpr
      ((change_env t r).mp (fallback r hr.1 hr.2.1))⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 唯一见证的原公式与力迫消去

唯一性以真正的一阶公式给出。实例化两个名称并连续消去蕴涵，取得同一条件
下的原子等号；有限参数以外的默认自由赋值不需要名称假设。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def unique_m {n} (φ : UnarySchema n) : Formula 1 n :=
  .forallE (.forallE (.imp (pred_m φ (fun i => .bound ⟨i.val+2, by omega⟩) (.bound 1))
    (.imp (pred_m φ (fun i => .bound ⟨i.val+2, by omega⟩) .newest) (Formula.extensionalEq (.bound 1) .newest))))
@[simp] theorem unique_closed_l {n} (φ : UnarySchema n) : (unique_m φ).FreeClosed := by
  simp -implicitDefEqProofs [unique_m, Definitional.Formula.FreeClosed]

theorem unique_sat_l (hE : Extensional M) {n} (φ : UnarySchema n) (ρ : Env M n) :
    Formula.satisfies ρ (unique_m φ) ↔ ∀ s t, φ.denote ρ s → φ.denote ρ t → s = t := by
  have he s t : (⟨fun i : Fin n => (Term.bound ⟨i.val+2, by omega⟩ : Term (n+2)).eval ((ρ.push s).push t),
      ((ρ.push s).push t).free⟩ : Env M n) = ρ := by cases ρ; rfl
  simp only [unique_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, pred_sat_l M, he,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_newest]
  rfl

theorem forced_unique_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {n p s t}
    (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i))
    (hs : Name_d M B s) (ht : Name_d M B t) (hp : M.mem p B) (hz : p ≠ z)
    (hU : Forces_d M B R z (unique_m φ) ρ p)
    (hsφ : Forces_d M B R z φ.body (ρ.push s) p) (htφ : Forces_d M B R z φ.body (ρ.push t) p) :
    Eq_force_d M B R z p s t := by
  let η : Env M n := ⟨ρ.bound, fun _ => s⟩
  let ξ := (η.push s).push t
  let e : Fin n → Term (n+2) := fun i => .bound ⟨i.val+2, by omega⟩
  let a := pred_m φ e (.bound 1)
  let b := pred_m φ e .newest
  let c : Formula 1 (n+2) := Formula.extensionalEq (.bound 1) .newest
  have he : (⟨fun i => (e i).eval ξ, ξ.free⟩ : Env M n) = η := by cases ρ; rfl
  have hn : ∀ v : Term (n+2), Name_d M B (v.eval ξ) := by
    intro v
    cases v with
    | free _ => exact hs
    | bound i => exact Fin.cases ht (Fin.cases hs hρ) i
  have hU := (forces_env_l hZF.1 _ (unique_closed_l φ) ρ η (fun _ => rfl) p).mp hU
  have hU := (forces_all_l hZF.1 _ η p).mp hU s hs
  have hU := (forces_all_l hZF.1 _ (η.push s) p).mp hU t ht
  have ha : Forces_d M B R z a ξ p := by
    rw [forces_pred_l hZF.1, he]
    exact (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push s) (η.push s) (fun _ => rfl) p).mp hsφ
  have hb : Forces_d M B R z b ξ p := by
    rw [forces_pred_l hZF.1, he]
    exact (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push t) (η.push t) (fun _ => rfl) p).mp htφ
  have hImp := forces_mp_l hZF.1 (forces_regular_l O hZF a ξ hn).1
    (forces_regular_l O hZF (.imp b c) ξ hn) hp hz hU ha
  have hEq := forces_mp_l hZF.1 (forces_regular_l O hZF b ξ hn).1 (forces_regular_l O hZF c ξ hn) hp hz hImp hb
  exact (code_eq_l M hZF.1 B R z (.bound 1) .newest ξ p).mp hEq

end YesMetaZFC.Model.Forcing.Internal
