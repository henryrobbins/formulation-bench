import Common
import problems.p11.formulations.a.Formulation
import problems.p11.formulations.b.Formulation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open BigOperators Finset

namespace P11

-- ============================================================================
-- § Parameter Mapping
-- ============================================================================

private def paramMap (p : P11.a.Params) : P11.b.Params :=
  { nT := p.nT
    nG := p.nG
    nW := p.nW
    nS := p.nS
    nL := p.nL
    ell := p.ell
    C_su := p.C_su
    P := p.P
    C := p.C
    C_fixed := p.C_fixed
    L := p.L
    R := p.R
    P_min := p.P_min
    P_max := p.P_max
    P_wind_min := p.P_wind_min
    P_wind_max := p.P_wind_max
    RU := p.RU
    RD := p.RD
    SU := p.SU
    SD := p.SD
    U := p.U
    D := p.D
    MR := p.MR
    hMR_bin := p.hMR_bin
    hT_pos := p.hT_pos
    hG_pos := p.hG_pos
    hW_pos := p.hW_pos
    hnS_pos := p.hnS_pos
    hnL_pos := p.hnL_pos
    hCsu_nn := p.hCsu_nn
    hP_nn := p.hP_nn
    hC_nn := p.hC_nn
    hCfixed_nn := p.hCfixed_nn
    hL_nn := p.hL_nn
    hR_nn := p.hR_nn
    hPmin_nn := p.hPmin_nn
    hPmax_nn := p.hPmax_nn
    hPmax_ge := p.hPmax_ge
    hPwmin_nn := p.hPwmin_nn
    hPwmax_nn := p.hPwmax_nn
    hPw_le := p.hPw_le
    hRU_nn := p.hRU_nn
    hRD_nn := p.hRD_nn
    hSU_nn := p.hSU_nn
    hSD_nn := p.hSD_nn
    hU_pos := p.hU_pos
    hD_pos := p.hD_pos }

-- ============================================================================
-- § Forward Mapping and Feasibility
-- ============================================================================

/--
**P11.a → P11.b**: keep the original schedule, set the EC1 indicator to the
conjunction of startup and next-period shutdown, and set reachable capacity to
the dispatched thermal output plus reserve.
-/
private def fwd (p : P11.a.Params) (v : P11.a.Vars p) :
    P11.b.Vars (paramMap p) :=
  { u := v.u
    v := v.v
    w := v.w
    d_su := v.d_su
    lam := v.lam
    p := v.p
    r := v.r
    c_var := v.c_var
    p_wind := v.p_wind
    b := fun g t =>
      v.v g ⟨t.val, by have := t.isLt; simp only [paramMap] at this; omega⟩ *
        v.w g ⟨t.val + 1, by have := t.isLt; simp only [paramMap] at this; omega⟩
    P_bar := fun g t =>
      p.P_min g * (v.u g t : ℝ) + v.p g t + v.r g t }

private lemma fwd_feas (p : P11.a.Params) (v : P11.a.Vars p)
    (h : P11.a.Feasible p v) :
    P11.b.Feasible (paramMap p) (fwd p v) := by
  refine
    { hdemand := h.hdemand
      hreserve := h.hreserve
      htransition := h.htransition
      hmin_up := h.hmin_up
      hmin_dn := h.hmin_dn
      hv_decomp := h.hv_decomp
      hlag := h.hlag
      hmust_run := h.hmust_run
      hcap_su := h.hcap_su
      hcap_sd := h.hcap_sd
      hramp_up := h.hramp_up
      hramp_dn := h.hramp_dn
      hp_eq := h.hp_eq
      hc_eq := h.hc_eq
      hlam_sum := h.hlam_sum
      hu_bin := h.hu_bin
      hv_bin := h.hv_bin
      hw_bin := h.hw_bin
      hd_bin := h.hd_bin
      hb_bin := ?_
      hlam_nn := h.hlam_nn
      hlam_le := h.hlam_le
      hp_nn := h.hp_nn
      hr_nn := h.hr_nn
      hcvar_nn := h.hcvar_nn
      hpwind_lo := h.hpwind_lo
      hpwind_hi := h.hpwind_hi
      hec1_ub_v := ?_
      hec1_ub_w := ?_
      hec1_lb := ?_
      hec2a := ?_
      hec2b := ?_
      hec2c := ?_
      hec3a := ?_
      hec3b := ?_
      hec3c := ?_
      hec4 := ?_ }
  · intro g t
    have ht : t.val + 1 < p.nT := by
      have := t.isLt
      simp only [paramMap] at this
      omega
    rcases h.hv_bin g ⟨t.val, by omega⟩ with hv | hv <;>
      rcases h.hw_bin g ⟨t.val + 1, ht⟩ with hw | hw <;>
      simp [fwd, hv, hw]
  · intro g t ht
    simp only [paramMap] at ht
    rcases h.hv_bin g t with hv | hv <;>
      rcases h.hw_bin g ⟨t.val + 1, ht⟩ with hw | hw <;>
      simp [fwd, hv, hw]
  · intro g t ht
    simp only [paramMap] at ht
    rcases h.hv_bin g t with hv | hv <;>
      rcases h.hw_bin g ⟨t.val + 1, ht⟩ with hw | hw <;>
      simp [fwd, hv, hw]
  · intro g t ht
    simp only [paramMap] at ht
    rcases h.hv_bin g t with hv | hv <;>
      rcases h.hw_bin g ⟨t.val + 1, ht⟩ with hw | hw <;>
      simp [fwd, hv, hw]
  · intro g t
    simp only [fwd, paramMap]
    linarith [h.hcap_su g t]
  · intro g t ht
    simp only [fwd, paramMap]
    linarith [h.hcap_sd g t ht]
  · intro g t ht
    simp only [paramMap] at ht
    have hsu := h.hcap_su g t
    have hsd := h.hcap_sd g t ht
    simp only [fwd, paramMap]
    rcases h.hv_bin g t with hv | hv <;>
      rcases h.hw_bin g ⟨t.val + 1, ht⟩ with hw | hw
    · simp [hv, hw] at hsu hsd ⊢
      linarith
    · simp [hv, hw] at hsu hsd ⊢
      linarith
    · simp [hv, hw] at hsu hsd ⊢
      linarith
    · simp [hv, hw] at hsu hsd ⊢
      by_cases hle :
          max (p.P_max g - p.SU g) 0 ≤ max (p.P_max g - p.SD g) 0
      · rw [min_eq_left hle]
        linarith
      · rw [min_eq_right (le_of_not_ge hle)]
        linarith
  · intro g t ht
    simp only [paramMap] at ht
    let prev : Fin p.nT := ⟨t.val - 1, by omega⟩
    have hrelax :
        0 ≤ (p.P_max g - p.P_min g) * (1 - (v.u g prev : ℝ)) := by
      rcases h.hu_bin g prev with hu | hu
      · rw [hu]
        norm_num
        exact p.hPmax_ge g
      · rw [hu]
        norm_num
    have hramp := h.hramp_up g t ht
    change
      p.P_min g * (v.u g t : ℝ) + v.p g t + v.r g t ≤
        p.P_min g * (v.u g t : ℝ) + v.p g prev + p.RU g +
          (p.P_max g - p.P_min g) * (1 - (v.u g prev : ℝ))
    linarith
  · intro g t ht
    simp only [paramMap] at ht
    let prev : Fin p.nT := ⟨t.val - 1, by omega⟩
    have hramp := h.hramp_up g t ht
    have hcap := h.hcap_su g prev
    have hrnn := h.hr_nn g prev
    change
      p.P_min g * (v.u g t : ℝ) + v.p g t + v.r g t ≤
        p.P_min g * (v.u g t : ℝ) +
          (p.P_max g - p.P_min g) * (v.u g prev : ℝ) -
            max (p.P_max g - p.SU g) 0 * (v.v g prev : ℝ) + p.RU g
    linarith
  · intro g t ht
    simp only [paramMap] at ht
    let prev : Fin p.nT := ⟨t.val - 1, by omega⟩
    have hprev_succ : prev.val + 1 < p.nT := by
      simp only [prev]
      omega
    have hnext : (⟨prev.val + 1, hprev_succ⟩ : Fin p.nT) = t := by
      apply Fin.ext
      simp only [prev]
      omega
    have hramp := h.hramp_up g t ht
    have hcap := h.hcap_sd g prev hprev_succ
    rw [hnext] at hcap
    have hrnn := h.hr_nn g prev
    change
      p.P_min g * (v.u g t : ℝ) + v.p g t + v.r g t ≤
        p.P_min g * (v.u g t : ℝ) +
          (p.P_max g - p.P_min g) * (v.u g prev : ℝ) -
            max (p.P_max g - p.SD g) 0 * (v.w g t : ℝ) + p.RU g
    linarith
  · intro t
    have hdemand := h.hdemand t
    have hreserve := h.hreserve t
    simp only [sum_add_distrib] at hdemand
    have hthermal :
        (∑ g : Fin p.nG, p.P_min g * (v.u g t : ℝ)) +
            ∑ g : Fin p.nG, v.p g t =
          p.L t - ∑ w : Fin p.nW, v.p_wind w t := by
      linarith [hdemand]
    simp only [fwd, paramMap, sum_add_distrib]
    linarith [hthermal, hreserve]

-- ============================================================================
-- § Backward Mapping and Feasibility
-- ============================================================================

/--
**P11.b → P11.a**: drop the two enhancement variables and their constraints.
-/
private def bwd (p : P11.a.Params) (v : P11.b.Vars (paramMap p)) :
    P11.a.Vars p :=
  { u := v.u
    v := v.v
    w := v.w
    d_su := v.d_su
    lam := v.lam
    p := v.p
    r := v.r
    c_var := v.c_var
    p_wind := v.p_wind }

private lemma bwd_feas (p : P11.a.Params) (v : P11.b.Vars (paramMap p))
    (h : P11.b.Feasible (paramMap p) v) :
    P11.a.Feasible p (bwd p v) := by
  simp only [bwd, paramMap] at *
  exact
    { hdemand := h.hdemand
      hreserve := h.hreserve
      htransition := h.htransition
      hmin_up := h.hmin_up
      hmin_dn := h.hmin_dn
      hv_decomp := h.hv_decomp
      hlag := h.hlag
      hmust_run := h.hmust_run
      hcap_su := h.hcap_su
      hcap_sd := h.hcap_sd
      hramp_up := h.hramp_up
      hramp_dn := h.hramp_dn
      hp_eq := h.hp_eq
      hc_eq := h.hc_eq
      hlam_sum := h.hlam_sum
      hu_bin := h.hu_bin
      hv_bin := h.hv_bin
      hw_bin := h.hw_bin
      hd_bin := h.hd_bin
      hlam_nn := h.hlam_nn
      hlam_le := h.hlam_le
      hp_nn := h.hp_nn
      hr_nn := h.hr_nn
      hcvar_nn := h.hcvar_nn
      hpwind_lo := h.hpwind_lo
      hpwind_hi := h.hpwind_hi }

-- ============================================================================
-- § Reformulation Structure
-- ============================================================================

def aBReformulation : MILPReformulation P11.a.formulation P11.b.formulation where
  paramMap := paramMap
  fwd := fwd
  bwd := bwd
  fwd_feas := fwd_feas
  bwd_feas := bwd_feas
  objMap := id
  objMap_mono := strictMono_id
  fwd_obj p v _ := by
    simp only [P11.a.formulation, P11.b.formulation, P11.a.obj, P11.b.obj,
      fwd, paramMap, id]
  bwd_obj p v _ := by
    simp only [P11.a.formulation, P11.b.formulation, P11.a.obj, P11.b.obj,
      bwd, paramMap, id]

end P11
