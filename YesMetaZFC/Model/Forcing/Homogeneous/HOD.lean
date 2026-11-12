import YesMetaZFC.Model.Forcing.Automorphism.RealSetName
import YesMetaZFC.Model.Forcing.Truth.ClosedTruth
import YesMetaZFC.Model.Forcing.CCC.Basic
import YesMetaZFC.SetTheory.InnerModel.OD.Parameters
import YesMetaZFC.Model.Forcing.Ground.Ordinals
import YesMetaZFC.SetTheory.InnerModel.OD.Separation
import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.InnerModel.HOD.Presentation

/-! # 弱齐性与地参数判定的一致性

任意两个正条件可经内部自同构变成相容条件。地参数的 check 名称以各自力迫条件
为基点，故无需最大条件；共同加强处的基点交换保证同一地参数命题不能得到相反判定。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Whom_d (B R z : M.Domain) : Prop := ∀ p q, M.mem p B → p ≠ z → M.mem q B → q ≠ z →
  ∃ F s, Aut_d M B R z F ∧ Entry_d M p s F ∧ Cmp_d M B R z s q

def whom_m {n} (B R z : Term n) : Formula 1 n :=
  Formula.forallMem B (Formula.forallMem B.weaken
    (.imp (.neg (Formula.extensionalEq (.bound 1) z.weaken.weaken))
      (.imp (.neg (Formula.extensionalEq .newest z.weaken.weaken))
        (.existsE (.existsE (.conj
          (aut_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
            z.weaken.weaken.weaken.weaken (.bound 1))
          (.conj (entry_m (.bound 3) .newest (.bound 1))
            (cmp_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
              z.weaken.weaken.weaken.weaken .newest (.bound 2)))))))))
derive_free_closed whom_m

theorem whom_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z : Term n) :
    Formula.satisfies ρ (whom_m B R z) ↔ Whom_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) := by
  simp only [whom_m, Whom_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, aut_sat_l hE,
    entry_sat_l M hE, cmp_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h p q hp hz hq hqz => h p hp q hq hz hqz, fun h p hp q hq hz hqz => h p q hp hz hq hqz⟩

/-- 基点与名称见证均量化；定义中没有预先指定的泛型或条件参数。 -/
def Gforce_d {n} (B R z : M.Domain) (φ : Formula 1 n) (v : Fin n → M.Domain) : Prop :=
  ∃ p, ∃ ρ : Env M n, M.mem p B ∧ p ≠ z ∧ (∀ i, Check_d M p (v i) (ρ.bound i)) ∧
    Forces_d M B R z φ ρ p

variable {M} {B R z : M.Domain} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem gforce_change_base_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (ρ : Env M n) {b p} (hb : M.mem b B)
    (hρ : ∀ i, Check_d M b (v i) (ρ.bound i)) (hp : Below_d M B R z p b)
    (hf : Forces_d M B R z φ ρ p) : Gforce_d M B R z φ v := by
  obtain ⟨η, hη, _⟩ := check_env_l hZF hp.1 v
  exact ⟨p, η, hp.1, hp.2.1, hη,
    (check_forces_bases_l O hZF φ hφ v ρ η hb hp.1 hρ hη hp (O.refl p hp.1)).mp hf⟩

/-- 弱齐性排除同一地参数正文的相反判定，包括没有最大条件的偏序。 -/
theorem whom_consistent_l (hH : Whom_d M B R z) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (h : Gforce_d M B R z φ v) : ¬ Gforce_d M B R z (.neg φ) v := by
  rintro ⟨q, η, hq, hqz, hη, hn⟩
  obtain ⟨p, ρ, hp, hpz, hρ, hf⟩ := h
  obtain ⟨F, s, hF, hps, r, hrs, hrq⟩ := hH p q hp hpz hq hqz
  have hs := (hF.domain p s hps).2
  obtain ⟨ξ, hξ, hξn⟩ := check_env_l hZF hs v
  have hfn := (aut_forces_closed_l hZF hF φ hφ ρ ξ
    (fun i => check_name_l M (check_range_l M hZF) hp (hρ i))
    (fun i => aut_check_l hZF hF hps (hρ i) (hξ i)) hps).mp hf
  have hrφ := (forces_regular_l O hZF φ ξ hξn).1 s r hs hrs hfn
  exact (forces_neg_l hZF.1 φ η q).mp hn r ⟨hrs.1, hrs.2.1, hrq⟩
    ((check_forces_bases_l O hZF φ hφ v ξ η hs hq hξ hη hrs hrq).mp hrφ)

end YesMetaZFC.Model.Forcing.Internal

/-! ## 地参数力迫的原公式

先量化正条件，再用有限存在块量化其 check 名称参数，最后调用原力迫翻译。
因而 Gforce 仅依赖完整力迫呈现与原地参数，不携带泛型或名称选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u

def gforce_m {n d} (φ : Formula 1 n) (B R z : Term d) (e : Fin n → Term d) : Formula 1 d :=
  .existsE (.conj (.mem .newest B.weaken)
    (.conj (.neg (Formula.extensionalEq .newest z.weaken))
      (od_ex_m n (.conj
        (lr_and_m (fun i : Fin n => check_m (lr_shift_l n .newest)
          (lr_shift_l n (e i).weaken) (.bound ⟨i.val, by omega⟩)))
        (force_at_m φ (fun i => .bound ⟨i.val, by omega⟩)
          (lr_shift_l n B.weaken) (lr_shift_l n R.weaken) (lr_shift_l n z.weaken)
          (lr_shift_l n .newest))))))

@[simp] theorem gforce_closed_l {n d} (φ : Formula 1 n) (B R z : Term d) (e : Fin n → Term d)
    (hφ : φ.FreeClosed) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hz : z.freeSupport = []) (he : ∀ i, (e i).freeSupport = []) : (gforce_m φ B R z e).FreeClosed := by
  simp only [gforce_m, Definitional.Formula.FreeClosed]
  refine ⟨⟨rfl, by simpa using hB⟩,
    (Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨rfl, by simpa using hz⟩, od_ex_closed_l n _ ?_⟩
  simp only [Definitional.Formula.FreeClosed]
  refine ⟨?_, force_at_closed_l _ _ _ _ _ _ hφ (fun _ => rfl)
    (by simpa using hB) (by simpa using hR) (by simpa using hz) (by simp)⟩
  exact lr_and_closed_l _ (fun i => check_m_freeClosed _ _ _ (by simp) (by simpa using he i) rfl)

theorem gforce_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n d}
    (φ : Formula 1 n) (hφ : φ.FreeClosed) (ρ : Env M d) (B R z : Term d) (e : Fin n → Term d) :
    Formula.satisfies ρ (gforce_m φ B R z e) ↔
      Gforce_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) φ (fun i => (e i).eval ρ) := by
  simp only [gforce_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    od_ex_sat_l, lr_and_sat_l, check_sat_l M hE, force_at_sat_l, lr_shift_sat_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  simp only [Definitional.Term.eval, lr_env_bound_l, lr_env_free_l]
  constructor
  · rintro ⟨p, hp, hpz, v, hv, hf⟩
    exact ⟨p, ⟨v, ρ.free⟩, hp, hpz, hv, hf⟩
  · rintro ⟨p, η, hp, hpz, hη, hf⟩
    exact ⟨p, hp, hpz, η.bound, hη,
      (forces_env_l hE φ hφ η ⟨η.bound, ρ.free⟩ (fun _ => rfl) p).mp hf⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 弱齐性下地参数真值的地模型定义

扩张真值先由真值引理给出泛型条件，再交换 check 基点。弱齐性排除相反判定，
因此存在条件力迫的原公式恰好计算每个泛型扩张的地参数真值。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
variable {b : M.Domain} (hb : U b) (e : M.Domain → (extension_l M hZF B R z U).Domain)
  (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x))
local notation "E" => extension_l M hZF B R z U
include O hU hb hv

theorem gforce_of_truth_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (η : Env E n) (hη : ∀ i, e (v i) = η.bound i)
    (ht : Formula.satisfies η φ) : Gforce_d M B R z φ v := by
  have hbB := (hU.proper b hb).1
  obtain ⟨ρ, hρ, hn⟩ := check_env_l hZF hbB v
  have hval := qenv_val_l (R := R) (z := z) (U := U) hZF ρ hn
  have heq i : (qenv_l hZF ρ hn).bound i = η.bound i :=
    (qval_unique_l (hv (v i) (ρ.bound i) (hρ i)) (hval (.bound i))).symm.trans (hη i)
  have hsat := (lr_env_congr_l φ hφ (qenv_l hZF ρ hn) η heq).mpr ht
  obtain ⟨p, hp, hf⟩ := (forcing_truth_l O hZF hU φ hφ ρ (qenv_l hZF ρ hn) hval).mpr hsat
  obtain ⟨q, hq, hqp, hqb⟩ := hU.directed p b hp hb
  have hq' := hU.proper q hq
  exact gforce_change_base_l O hZF φ hφ v ρ hbB hρ ⟨hq'.1, hq'.2, hqb⟩
    ((forces_regular_l O hZF φ ρ hn).1 p q (hU.proper p hp).1 ⟨hq'.1, hq'.2, hqp⟩ hf)

/-- 右侧是泛型扩张真值，左侧是完全不含泛型参数的地模型原公式。 -/
theorem whom_ground_truth_l (hH : Whom_d M B R z) {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (v : Fin n → M.Domain) (η : Env E n) (hη : ∀ i, e (v i) = η.bound i) :
    Gforce_d M B R z φ v ↔ Formula.satisfies η φ := by
  refine ⟨fun h => ?_, gforce_of_truth_l O hZF hU hb e hv φ hφ v η hη⟩
  apply Classical.byContradiction
  intro hn
  exact whom_consistent_l O hZF hH φ hφ v h
    (gforce_of_truth_l O hZF hU hb e hv (.neg φ) (by simpa only [Definitional.Formula.FreeClosed] using hφ) v η hη
      ((Formula.satisfies_neg_iff η φ).mpr hn))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 弱齐性下的可定义旧集合子集恢复

对地模型定义的 Gforce 原公式作分离。弱齐性真值对应证明所得旧集合的像恰为
目标子集；若完整力迫呈现与定义参数在 OD[A] 中，同一分离定义仍在 OD[A] 中。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
variable {b : M.Domain} (hb : U b) (e : M.Domain → (extension_l M hZF B R z U).Domain)
  (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x))
  (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y)
local notation "E" => extension_l M hZF B R z U
include O hU hb hv he

/-- 更一般的恢复：旧集合中、由旧参数定义的子集在弱齐性扩张中仍是旧集合。 -/
theorem whom_definable_subset_l (hH : Whom_d M B R z) {A D}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z) (hD : Ob_d A D)
    {n} (φ : UnarySchema n) (ρ : Env M n) (η : Env E n)
    (hρ : ∀ i, Ob_d A (ρ.bound i)) (hη : ∀ i, e (ρ.bound i) = η.bound i)
    {X : (E).Domain} (hX : (E).MemberSubset X (e D))
    (hφ : ∀ y, φ.denote η y ↔ y ∈ X) : ∃ Y, Ob_d A Y ∧ e Y = X := by
  let δ := ((ρ.push B).push R).push z
  let ψ : UnarySchema (n+3) := {
    body := gforce_m φ.body (.bound 3) (.bound 2) (.bound 1)
      (Fin.cases .newest (fun i => .bound ⟨i.val+4, by omega⟩))
    freeClosed := gforce_closed_l _ _ _ _ _ φ.freeClosed rfl rfl rfl (Fin.cases rfl (fun _ => rfl)) }
  have hψ a : ψ.denote δ a ↔ Gforce_d M B R z φ.body (ρ.push a).bound := by
    let f : Fin (n+1) → Term (n+4) := Fin.cases .newest (fun i => .bound ⟨i.val+4, by omega⟩)
    have hf : (fun i => (f i).eval (δ.push a)) = (ρ.push a).bound :=
      funext (Fin.cases rfl (fun _ => rfl))
    exact (gforce_sat_l hZF.1 φ.body φ.freeClosed (δ.push a) (.bound 3) (.bound 2) (.bound 1) f).trans
      (by change Gforce_d M B R z φ.body _ ↔ _; rw [hf])
  obtain ⟨Y, hy⟩ := ZF.separation_exists_d hZF ψ δ D
  have defn T : (oa_sep_s ψ).denote (δ.push D) T ↔ T = Y :=
    (oa_sep_schema_l ψ δ D T).trans
      ⟨fun ht => hZF.1.eq_of_same_members T Y (fun a => (ht a).trans (hy a).symm), fun ht => ht.symm ▸ hy⟩
  have hY := ob_closed_l hZF A (oa_sep_s ψ) (δ.push D)
    (Fin.cases hD (Fin.cases hz (Fin.cases hR (Fin.cases hB hρ)))) defn
  have truth a : ψ.denote δ a ↔ e a ∈ X := (hψ a).trans
    ((whom_ground_truth_l O hZF hU hb e hv hH φ.body φ.freeClosed (ρ.push a).bound (η.push (e a))
      (Fin.cases rfl hη)).trans (hφ (e a)))
  refine ⟨Y, hY, (extension_ext_l O hZF hU).eq_of_same_members (e Y) X (fun y => ?_)⟩
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := (he Y y).mp h
    exact (truth a).mp ((hy a).mp ha).2
  · intro h
    obtain ⟨a, ha, rfl⟩ := (he D y).mp (hX y h)
    exact (he Y (e a)).mpr ⟨a, (hy a).mpr ⟨ha, (truth a).mpr h⟩, rfl⟩

/-- 唯一定义某集合的正文，转为定义该集合成员的正文。 -/
def od_member_s {n} (φ : UnarySchema n) : UnarySchema n := {
  body := .existsE (.conj (pred_m φ (fun i => .bound ⟨i.val+2, by omega⟩) .newest)
    (.mem (.bound 1) .newest)) }

omit O hU hb e hv he in
theorem od_member_sat_l {N : SetTheory.Structure.{u}} {n} (φ : UnarySchema n) (η : Env N n)
    {X} (h : ∀ y, φ.denote η y ↔ y = X) (x : N.Domain) :
    (od_member_s φ).denote η x ↔ N.mem x X := by
  simp only [od_member_s, UnarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, pred_sat_l, Formula.satisfies_mem_iff]
  change (∃ y, φ.denote η y ∧ N.mem x y) ↔ N.mem x X
  exact ⟨fun ⟨y, hy, hx⟩ => (h y).mp hy ▸ hx, fun hx => ⟨X, (h X).mpr rfl, hx⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## OD 序数子集的恢复

先用不增加序数把序数参数与子集的序数界拉回地模型，再用弱齐性真值公式作分离。
相对版本保留固定的整个集合参数 A；无参数结论只需完整力迫呈现在地模型中 OD。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
variable {b : M.Domain} (hb : U b) (e : M.Domain → (extension_l M hZF B R z U).Domain)
  (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x))
  (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) (hi : Function.Injective e)
local notation "E" => extension_l M hZF B R z U
include O hU hb hv he hi

/-- 扩张中的任意序数集合都包含于一个旧序数，不预先要求给出界。 -/
theorem ordinal_set_ground_bound_l (X : (E).Domain) (hX : ∀ x, x ∈ X → (E).IsOrdinal x) :
    ∃ α, M.IsOrdinal α ∧ (E).MemberSubset X (e α) := by
  let hE := preserves_zf_l O hZF hU
  obtain ⟨T, hT⟩ := KP.exists_union (ZF.modelsKP hE) X
  have hTo := Structure.IsOrdinal.of_union (ZF.modelsKP hE) hT hX
  obtain ⟨D, hD⟩ := KP.exists_successor (ZF.modelsKP hE) T
  have hDo := KP.successor_isOrdinal (ZF.modelsKP hE) hTo hD
  obtain ⟨α, hα, hαD⟩ := no_new_ordinals_l O hZF hU (hU.proper b hb).1 e hv he hi hDo
  refine ⟨α, hα, fun x hx => ?_⟩
  rw [hαD]
  have hsub : (E).MemberSubset x T := fun y hy => (hT y).mpr ⟨x, hx, hy⟩
  rcases ordinal_subset_cases_l (ZF.modelsKP hE) (hX x hx) hTo hsub with hh | hh
  · exact hh.symm ▸ hD.predecessor_mem
  · exact (hD x).mpr (Or.inl hh)

/-- 任意 OD[A] 旧集合的 OD[e(A)] 子集均能恢复，包括序数代码的有序对关系。 -/
theorem whom_ob_old_subset_l (hH : Whom_d M B R z) {A D}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z) (hD : Ob_d A D)
    {X : (E).Domain} (hX : Ob_d (e A) X) (hsub : (E).MemberSubset X (e D)) :
    ∃ Y, Ob_d A Y ∧ e Y = X := by
  let hE := preserves_zf_l O hZF hU
  obtain ⟨n, φ, η, hη, hdef⟩ := (ob_iff_external_l hE).mp hX
  obtain ⟨v, hv'⟩ := Classical.axiomOfChoice (fun i =>
    no_new_ordinals_l O hZF hU (hU.proper b hb).1 e hv he hi (hη i))
  let ρ : Env M n := ⟨v, fun _ => A⟩
  let ψ : UnarySchema (n+1) := ⟨φ.body, φ.freeClosed⟩
  have hψ y : ψ.denote (η.push (e A)) y ↔ y = X := hdef y
  exact whom_definable_subset_l O hZF hU hb e hv he hH hB hR hz hD
    (od_member_s ψ) (ρ.push A) (η.push (e A))
    (Fin.cases (ob_parameter_l hZF A) (fun i => ob_ordinal_l hZF A (hv' i).1))
    (Fin.cases rfl (fun i => (hv' i).2)) hsub (od_member_sat_l ψ _ hψ)

/-- 弱齐性、OD[A] 呈现的扩张中，每个 OD[e(A)] 序数子集来自地模型 OD[A]。 -/
theorem whom_ob_ordinal_subset_l (hH : Whom_d M B R z) {A}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z)
    {X : (E).Domain} (hX : Ob_d (e A) X) (hOrd : ∀ x, x ∈ X → (E).IsOrdinal x) :
    ∃ Y, Ob_d A Y ∧ e Y = X := by
  obtain ⟨α, hα, hXα⟩ := ordinal_set_ground_bound_l O hZF hU hb e hv he hi X hOrd
  exact whom_ob_old_subset_l O hZF hU hb e hv he hi hH hB hR hz (ob_ordinal_l hZF A hα) hX hXα

/-- 无参数版本：OD 弱齐性力迫不增加 OD 序数子集，且原像仍是地模型中的 OD 集。 -/
theorem whom_od_ordinal_subset_l (hH : Whom_d M B R z)
    (hB : Od_d B) (hR : Od_d R) (hz : Od_d z)
    {X : (E).Domain} (hX : Od_d X) (hOrd : ∀ x, x ∈ X → (E).IsOrdinal x) :
    ∃ Y, Od_d Y ∧ e Y = X := by
  let hE := preserves_zf_l O hZF hU
  obtain ⟨A, hA⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨Y, hY, hYX⟩ := whom_ob_ordinal_subset_l O hZF hU hb e hv he hi hH
    (ob_of_od_l hZF A hB) (ob_of_od_l hZF A hR) (ob_of_od_l hZF A hz) (ob_of_od_l hE (e A) hX) hOrd
  exact ⟨Y, (ob_ordinal_parameter_l hZF (Structure.IsOrdinal.of_no_members hA)).mp hY, hYX⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 弱齐性力迫的 HOD 比较

把 HOD[e(A)] 对象呈现为序数代码上的隶属关系，用弱齐性恢复载体与关系，再在
地模型内部坍塌。目标模型的内部唯一性把原对象识别为地模型 HOD[A] 对象的像。
全程只需背景 ZF，不要求模型外部良基，也不要求偏序具有最大条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
variable {b : M.Domain} (hb : U b) (e : M.Domain → (extension_l M hZF B R z U).Domain)
  (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x))
  (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) (hi : Function.Injective e)
local notation "E" => extension_l M hZF B R z U
include O hU hb hv he hi

/-- 固定参数比较：HOD[e(A)] 的每个对象来自地模型 HOD[A]。 -/
theorem whom_hb_l (hH : Whom_d M B R z) {A}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z)
    {x : (E).Domain} (hx : Hb_d (e A) x) : ∃ y, Hb_d A y ∧ e y = x := by
  let hE := preserves_zf_l O hZF hU
  -- 先把整个遗传容器的隶属关系呈现在有界序数码上。
  obtain ⟨κ, C, S, T, F, hκ, hCκ, hS, hoC, hoS, fn, hg, hx⟩ := hb_presentation_l hE hx
  obtain ⟨α, hα, hακ⟩ := no_new_ordinals_l O hZF hU (hU.proper b hb).1 e hv he hi hκ
  subst κ
  -- 载体是旧序数的可定义子集；关系是旧笛卡尔积的可定义子集。
  obtain ⟨C₀, hoC₀, eqC⟩ := whom_ob_old_subset_l O hZF hU hb e hv he hi hH hB hR hz
    (ob_ordinal_l hZF A hα) hoC hCκ
  subst C
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF (kp_pair_l (ZF.modelsKP hZF)) α α
  have hp := image_product_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) e hi he hP
  have hs : (E).MemberSubset S (e P) := by
    intro p hpS
    obtain ⟨a, b, ha, hb, hab⟩ := hS p hpS
    exact (hp p).mpr ⟨a, hCκ a ha, b, hCκ b hb, hab⟩
  obtain ⟨S₀, hoS₀, eqS⟩ := whom_ob_old_subset_l O hZF hU hb e hv he hi hH hB hR hz
    (ob_product_l hZF A (ob_ordinal_l hZF A hα) (ob_ordinal_l hZF A hα) hP) hoS hs
  subst S
  -- 对同一旧关系在两模型内坍塌，以目标模型中的唯一性识别原对象。
  exact collapse_hb_recover_l e hi he hZF hE hoC₀ hoS₀ (fun a ha => ob_ordinal_l hZF A
    (hα.mem ((image_member_l e hi he).mp (hCκ (e a) ((he C₀ (e a)).mpr ⟨a, ha, rfl⟩))))) fn hg hx

/-- 无参数比较：完整力迫呈现为 OD 时，HOD 的包含方向从扩张指向地模型。 -/
theorem whom_hod_l (hH : Whom_d M B R z) (hB : Od_d B) (hR : Od_d R) (hz : Od_d z)
    {x : (E).Domain} (hx : Hod_d x) : ∃ y, Hod_d y ∧ e y = x := by
  obtain ⟨A, hA⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨y, hy, hyx⟩ := whom_hb_l O hZF hU hb e hv he hi hH
    (ob_of_od_l hZF A hB) (ob_of_od_l hZF A hR) (ob_of_od_l hZF A hz)
    (hb_of_hod_l (preserves_zf_l O hZF hU) (e A) hx)
  exact ⟨y, (hb_ordinal_parameter_l hZF (Structure.IsOrdinal.of_no_members hA)).mp hy, hyx⟩

omit hb e hv he hi in
/-- 固定参数版本同样自动构造嵌入，呈现只需属于 OD[A]。 -/
theorem whom_hb_comparison_l (hH : Whom_d M B R z) {A}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z) :
    ∃ e : M.Domain → (E).Domain, Function.Injective e ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧
      (∀ x, (E).IsOrdinal x ↔ ∃ α, M.IsOrdinal α ∧ e α = x) ∧
      ∀ x : (E).Domain, Hb_d (e A) x → ∃ y, Hb_d A y ∧ e y = x := by
  obtain ⟨b, hb⟩ := hU.inhabited
  obtain ⟨e, hv, he, hi, ho⟩ := check_map_ordinals_l O hZF hU hb
  exact ⟨e, hi, he, ho, fun _ hx => whom_hb_l O hZF hU hb e hv he hi hH hB hR hz hx⟩

omit hb e hv he hi in
/-- 自动构造地嵌入，并同时给出序数相同及 HOD 比较；无额外坍塌或编码前提。 -/
theorem whom_hod_comparison_l (hH : Whom_d M B R z) (hB : Od_d B) (hR : Od_d R) (hz : Od_d z) :
    ∃ e : M.Domain → (E).Domain, Function.Injective e ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧
      (∀ x, (E).IsOrdinal x ↔ ∃ α, M.IsOrdinal α ∧ e α = x) ∧
      ∀ x : (E).Domain, Hod_d x → ∃ y, Hod_d y ∧ e y = x := by
  obtain ⟨b, hb⟩ := hU.inhabited
  obtain ⟨e, hv, he, hi, ho⟩ := check_map_ordinals_l O hZF hU hb
  exact ⟨e, hi, he, ho, fun _ hx => whom_hod_l O hZF hU hb e hv he hi hH hB hR hz hx⟩

end YesMetaZFC.Model.Forcing.Internal
